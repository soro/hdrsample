use core::Counter;
use core::HistogramSettings;
use iterators::{self, HistogramIterator};
use num::ToPrimitive;

// once associated type defaults make it in this should become an associated type - would clean up a lot of interfaes
pub trait Histogram<T: Counter> : Sized {
    /// Get settings
    fn settings<'a>(&'a self) -> &'a HistogramSettings;

    /// Get the current number of distinct values that can be represented in the histogram.
    fn len(&self) -> usize;

    /// Get the total number of samples recorded.
    fn count(&self) -> u64;

    /// Returns count at index, or None if out of bounds
    fn count_at_index(&self, index: usize) -> Option<T>;

    /// Returns an error if the index doesn't exist.
    fn set_count_at_index(&mut self, index: usize, count: T) -> Result<(), ()>;

    /// Get the index of the last histogram bin.
    fn last_index(&self) -> usize {
        self.len().checked_sub(1).expect("Empty counts array?")
    }

    // ********************************************************************************************
    // Getters for settings values
    // ********************************************************************************************
    fn auto_resize(&self) -> bool {
        self.settings().auto_resize
    }

    /// Get the lowest discernible value for the histogram in its current configuration.
    fn low(&self) -> u64 {
        self.settings().lowest_discernible_value
    }

    /// Get the highest trackable value for the histogram in its current configuration.
    fn high(&self) -> u64 {
        self.settings().highest_trackable_value
    }

    /// Get the number of significant value digits kept by this histogram.
    fn sigfig(&self) -> u8 {
        self.settings().significant_value_digits
    }

    /// Get the number of buckets used by the histogram to cover the highest trackable value.
    ///
    /// This method differs from `.len()` in that it does not count the sub buckets within each
    /// bucket.
    ///
    /// This method is probably only useful for testing purposes.
    fn buckets(&self) -> u8 {
        self.settings().bucket_count
    }

    // ********************************************************************************************
    // Methods for looking up the count for a given value/index
    // ********************************************************************************************

    /// Find the bucket the given value should be placed in.
    /// Returns `None` if the corresponding index cannot be represented in `usize`.
    fn index_for(&self, value: u64) -> Option<usize> {
        let bucket_index = self.bucket_for(value);
        let sub_bucket_index = self.sub_bucket_for(value, bucket_index);
        let settings = self.settings();

        debug_assert!(sub_bucket_index < settings.sub_bucket_count);
        debug_assert!(bucket_index == 0 || (sub_bucket_index >= settings.sub_bucket_half_count));

        // Calculate the index for the first entry that will be used in the bucket (halfway through
        // sub_bucket_count). For bucket_index 0, all sub_bucket_count entries may be used, but
        // bucket_base_index is still set in the middle.
        let bucket_base_index = (bucket_index as i32 + 1) << settings.sub_bucket_half_count_magnitude;

        // Calculate the offset in the bucket. This subtraction will result in a positive value in
        // all buckets except the 0th bucket (since a value in that bucket may be less than half
        // the bucket's 0 to sub_bucket_count range). However, this works out since we give bucket 0
        // twice as much space.
        let offset_in_bucket = sub_bucket_index as i32 - settings.sub_bucket_half_count as i32;

        let index = bucket_base_index + offset_in_bucket;
        // This is always non-negative because offset_in_bucket is only negative (and only then by
        // sub_bucket_half_count at most) for bucket 0, and bucket_base_index will be halfway into
        // bucket 0's sub buckets in that case.
        debug_assert!(index >= 0);
        return index.to_usize();
    }


    /// Compute the lowest (and therefore highest precision) bucket index whose sub-buckets can
    /// represent the value.
    #[inline]
    fn bucket_for(&self, value: u64) -> u8 {
        // Calculates the number of powers of two by which the value is greater than the biggest
        // value that fits in bucket 0. This is the bucket index since each successive bucket can
        // hold a value 2x greater. The mask maps small values to bucket 0.
        // Will not underflow because sub_bucket_mask caps the leading zeros to no more than
        // leading_zero_count_base.
        self.settings().leading_zero_count_base - (value | self.settings().sub_bucket_mask).leading_zeros() as u8
    }

    /// Compute the position inside a bucket at which the given value should be recorded, indexed
    /// from position 0 in the bucket (in the first half, which is not used past the first bucket).
    /// For bucket_index > 0, the result will be in the top half of the bucket.
    #[inline]
    fn sub_bucket_for(&self, value: u64, bucket_index: u8) -> u32 {
        // Since bucket_index is simply how many powers of 2 greater value is than what will fit in
        // bucket 0 (that is, what will fit in [0, sub_bucket_count)), we shift off that many
        // powers of two, and end up with a number in [0, sub_bucket_count).
        // For bucket_index 0, this is just value. For bucket index k > 0, we know value won't fit
        // in bucket (k - 1) by definition, so this calculation won't end up in the lower half of
        // [0, sub_bucket_count) because that would mean it would also fit in bucket (k - 1).
        // As unit magnitude grows, the maximum possible bucket index should shrink because it is
        // based off of sub_bucket_mask, so this shouldn't lead to an overlarge shift.
        (value >> (bucket_index + self.settings().unit_magnitude)) as u32
    }

    /// Find the number of buckets needed such that `value` is representable.
    fn buckets_to_cover(&self, value: u64) -> u8 {
        // Shift won't overflow because sub_bucket_magnitude + unit_magnitude <= 63.
        // the k'th bucket can express from 0 * 2^k to sub_bucket_count * 2^k in units of 2^k
        let mut smallest_untrackable_value = (self.settings().sub_bucket_count as u64) << self.settings().unit_magnitude;

        // always have at least 1 bucket
        let mut buckets_needed = 1;
        while smallest_untrackable_value <= value {
            if smallest_untrackable_value > u64::max_value() / 2 {
                // next shift will overflow, meaning that bucket could represent values up to ones
                // greater than i64::max_value, so it's the last bucket
                return buckets_needed + 1;
            }
            smallest_untrackable_value <<= 1;
            buckets_needed += 1;
        }
        buckets_needed
    }

    /// Compute the value corresponding to the provided bucket and sub bucket indices.
    /// The indices given must map to an actual u64; providing contrived indices that would map to
    /// a value larger than u64::max_value() will yield garbage.
    #[inline]
    fn value_from_loc(&self, bucket_index: u8, sub_bucket_index: u32) -> u64 {
        // Sum won't overflow; bucket_index and unit_magnitude are both <= 64.
        // However, the resulting shift may overflow given bogus input, e.g. if unit magnitude is
        // large and the input sub_bucket_index is for an entry in the counts index that shouldn't
        // be used (because this calculation will overflow).
        (sub_bucket_index as u64) << (bucket_index + self.settings().unit_magnitude)
    }

    /// Get the lowest value that is equivalent to the given value within the histogram's
    /// resolution. Equivalent here means that value samples recorded for any two equivalent values
    /// are counted in a common total count.
    fn lowest_equivalent(&self, value: u64) -> u64 {
        let bucket_index = self.bucket_for(value);
        let sub_bucket_index = self.sub_bucket_for(value, bucket_index);
        self.value_from_loc(bucket_index, sub_bucket_index)
    }

    /// Get the highest value that is equivalent to the given value within the histogram's
    /// resolution. Equivalent here means that value samples recorded for any two equivalent values
    /// are counted in a common total count.
    ///
    /// Note that the return value is capped at `u64::max_value()`.
    fn highest_equivalent(&self, value: u64) -> u64 {
        if value == u64::max_value() {
            u64::max_value()
        } else {
            self.next_non_equivalent(value) - 1
        }
    }

    /// Get a value that lies in the middle (rounded up) of the range of values equivalent the
    /// given value. Equivalent here means that value samples recorded for any two equivalent
    /// values are counted in a common total count.
    ///
    /// Note that the return value is capped at `u64::max_value()`.
    fn median_equivalent(&self, value: u64) -> u64 {
        // adding half of the range to the bottom of the range shouldn't overflow
        self.lowest_equivalent(value).checked_add(self.equivalent_range(value) >> 1)
            .expect("median equivalent should not overflow")
    }

    /// Get the next value that is *not* equivalent to the given value within the histogram's
    /// resolution. Equivalent means that value samples recorded for any two equivalent values are
    /// counted in a common total count.
    ///
    /// Note that the return value is capped at `u64::max_value()`.
    fn next_non_equivalent(&self, value: u64) -> u64 {
        self.lowest_equivalent(value).saturating_add(self.equivalent_range(value))
    }

    /// Get the size (in value units) of the range of values that are equivalent to the given value
    /// within the histogram's resolution. Equivalent here means that value samples recorded for
    /// any two equivalent values are counted in a common total count.
    fn equivalent_range(&self, value: u64) -> u64 {
        let bucket_index = self.bucket_for(value);
        1_u64 << self.settings().unit_magnitude + bucket_index
    }

    /// Determine if two values are equivalent with the histogram's resolution. Equivalent here
    /// means that value samples recorded for any two equivalent values are counted in a common
    /// total count.
    fn equivalent(&self, value1: u64, value2: u64) -> bool {
        self.lowest_equivalent(value1) == self.lowest_equivalent(value2)
    }

    /// Computes the matching histogram value for the given histogram bin.
    ///
    /// `index` must be no larger than `u32::max_value()`; no possible histogram uses that much
    /// storage anyway. So, any index that comes from a valid histogram location will be safe.
    ///
    /// If the index is for a position beyond what this histogram is configured for, the correct
    /// corresponding value will be returned, but of course it won't have a corresponding count.
    ///
    /// If the index maps to a value beyond `u64::max_value()`, the result will be garbage.
    fn value_for(&self, index: usize) -> u64 {
        // Dividing by sub bucket half count will yield 1 in top half of first bucket, 2 in
        // in the top half (i.e., the only half that's used) of the 2nd bucket, etc, so subtract 1
        // to get 0-indexed bucket indexes. This will be -1 for the bottom half of the first bucket.
        let mut bucket_index = (index >> self.settings().sub_bucket_half_count_magnitude) as isize - 1;

        // Calculate the remainder of dividing by sub_bucket_half_count, shifted into the top half
        // of the corresponding bucket. This will (temporarily) map indexes in the lower half of
        // first bucket into the top half.

        // The subtraction won't underflow because half count is always at least 1.
        // TODO precalculate sub_bucket_half_count mask if benchmarks show improvement
        let mut sub_bucket_index =
            ((index.to_u32().expect("index must fit in u32")) & (self.settings().sub_bucket_half_count - 1))
                + self.settings().sub_bucket_half_count;
        if bucket_index < 0 {
            // lower half of first bucket case; move sub bucket index back
            sub_bucket_index -= self.settings().sub_bucket_half_count;
            bucket_index = 0;
        }
        self.value_from_loc(bucket_index as u8, sub_bucket_index)

    }

    /// Compute the actual number of bins to use for the given bucket count (that is, including the
    /// sub-buckets within each top-level bucket).
    ///
    /// If we have `N` such that `sub_bucket_count * 2^N > high`, we need storage for `N+1` buckets,
    /// each with enough slots to hold the top half of the `sub_bucket_count` (the lower half is
    /// covered by previous buckets), and the +1 being used for the lower half of the 0'th bucket.
    /// Or, equivalently, we need 1 more bucket to capture the max value if we consider the
    /// sub-bucket length to be halved.
    fn num_bins(&self, number_of_buckets: u8) -> u32 {
        (number_of_buckets as u32 + 1) * (self.settings().sub_bucket_half_count)
    }

    /// Get the computed mean value of all recorded values in the histogram.
    fn mean(&self) -> f64 {
        let count = self.count();
        if count == 0 {
            return 0.0;
        }

        self.iter_recorded().fold(0.0_f64, |total, v| {
            // TODO overflow?
            total +
                self.median_equivalent(v.value()) as f64 * v.count_at_value().as_f64()
                    / count as f64
        })
    }

    /// Get the computed standard deviation of all recorded values in the histogram
    fn stdev(&self) -> f64 {
        let count = self.count();
        if count == 0 {
            return 0.0;
        }

        let mean = self.mean();
        let geom_dev_tot = self.iter_recorded().fold(0.0_f64, |gdt, v| {
            let dev = self.median_equivalent(v.value()) as f64 - mean;
            gdt + (dev * dev) * v.count_since_last_iteration() as f64
        });

        (geom_dev_tot / count as f64).sqrt()
    }



    // ********************************************************************************************
    // Iterators
    // ********************************************************************************************

    /// Iterate through histogram values by quantile levels.
    ///
    /// The iteration mechanic for this iterator may appear somewhat confusing, but it yields
    /// fairly pleasing output. The iterator starts with a *quantile step size* of
    /// `1/halving_period`. For every iteration, it yields a value whose quantile is that much
    /// greater than the previously emitted quantile (i.e., initially 0, 0.1, 0.2, etc.). Once
    /// `halving_period` values have been emitted, the quantile  step size is halved, and the
    /// iteration continues.
    ///
    /// `ticks_per_half_distance` must be at least 1.
    ///
    /// The iterator yields an `iterators::IterationValue` struct.
    ///
    /// ```
    /// use hdrsample::Histogram;
    /// use hdrsample::iterators::IterationValue;
    /// let mut hist = Histogram::<u64>::new_with_max(10000, 4).unwrap();
    /// for i in 0..10000 {
    ///     hist += i;
    /// }
    ///
    /// let mut perc = hist.iter_quantiles(1);
    ///
    /// println!("{:?}", hist.iter_quantiles(1).collect::<Vec<_>>());
    ///
    /// assert_eq!(perc.next(), Some(IterationValue::new(hist.value_at_quantile(0.0001), 0.0001, 1, 1)));
    /// // step size = 50
    /// assert_eq!(perc.next(), Some(IterationValue::new(hist.value_at_quantile(0.5), 0.5, 1, 5000 - 1)));
    /// // step size = 25
    /// assert_eq!(perc.next(), Some(IterationValue::new(hist.value_at_quantile(0.75), 0.75, 1, 2500)));
    /// // step size = 12.5
    /// assert_eq!(perc.next(), Some(IterationValue::new(hist.value_at_quantile(0.875), 0.875, 1, 1250)));
    /// // step size = 6.25
    /// assert_eq!(perc.next(), Some(IterationValue::new(hist.value_at_quantile(0.9375), 0.9375, 1, 625)));
    /// // step size = 3.125
    /// assert_eq!(perc.next(), Some(IterationValue::new(hist.value_at_quantile(0.9688), 0.9688, 1, 313)));
    /// // etc...
    /// ```
    fn iter_quantiles<'a>(&'a self, ticks_per_half_distance: u32) -> HistogramIterator<'a, T, iterators::quantile::Iter<'a, T, Self>, Self> {
        iterators::quantile::Iter::new(self, ticks_per_half_distance)
    }

    /// Iterates through histogram values using linear value steps. The iteration is performed in
    /// steps of size `step`, each one yielding the count for all values in the preceeding value
    /// range of size `step`. The iterator terminates when all recorded histogram values are
    /// exhausted.
    ///
    /// The iterator yields an `iterators::IterationValue` struct.
    ///
    /// ```
    /// use hdrsample::Histogram;
    /// use hdrsample::iterators::IterationValue;
    /// let mut hist = Histogram::<u64>::new_with_max(1000, 3).unwrap();
    /// hist += 100;
    /// hist += 500;
    /// hist += 800;
    /// hist += 850;
    ///
    /// let mut perc = hist.iter_linear(100);
    /// assert_eq!(perc.next(), Some(IterationValue::new(99, hist.quantile_below(99), 0, 0)));
    /// assert_eq!(perc.next(), Some(IterationValue::new(199, hist.quantile_below(199), 0, 1)));
    /// assert_eq!(perc.next(), Some(IterationValue::new(299, hist.quantile_below(299), 0, 0)));
    /// assert_eq!(perc.next(), Some(IterationValue::new(399, hist.quantile_below(399), 0, 0)));
    /// assert_eq!(perc.next(), Some(IterationValue::new(499, hist.quantile_below(499), 0, 0)));
    /// assert_eq!(perc.next(), Some(IterationValue::new(599, hist.quantile_below(599), 0, 1)));
    /// assert_eq!(perc.next(), Some(IterationValue::new(699, hist.quantile_below(699), 0, 0)));
    /// assert_eq!(perc.next(), Some(IterationValue::new(799, hist.quantile_below(799), 0, 0)));
    /// assert_eq!(perc.next(), Some(IterationValue::new(899, hist.quantile_below(899), 0, 2)));
    /// assert_eq!(perc.next(), None);
    /// ```
    fn iter_linear<'a>(&'a self, step: u64)
            -> HistogramIterator<'a, T, iterators::linear::Iter<'a, T, Self>, Self> {
        iterators::linear::Iter::new(self, step)
    }

    /// Iterates through histogram values at logarithmically increasing levels. The iteration is
    /// performed in steps that start at `start` and increase exponentially according to `exp`. The
    /// iterator terminates when all recorded histogram values are exhausted.
    ///
    /// The iterator yields an `iterators::IterationValue` struct.
    ///
    /// ```
    /// use hdrsample::Histogram;
    /// use hdrsample::iterators::IterationValue;
    /// let mut hist = Histogram::<u64>::new_with_max(1000, 3).unwrap();
    /// hist += 100;
    /// hist += 500;
    /// hist += 800;
    /// hist += 850;
    ///
    /// let mut perc = hist.iter_log(1, 10.0);
    /// assert_eq!(perc.next(), Some(IterationValue::new(0, hist.quantile_below(0), 0, 0)));
    /// assert_eq!(perc.next(), Some(IterationValue::new(9, hist.quantile_below(9), 0, 0)));
    /// assert_eq!(perc.next(), Some(IterationValue::new(99, hist.quantile_below(99), 0, 0)));
    /// assert_eq!(perc.next(), Some(IterationValue::new(999, hist.quantile_below(999), 0, 4)));
    /// assert_eq!(perc.next(), None);
    /// ```
    fn iter_log<'a>(&'a self, start: u64, exp: f64)
            -> HistogramIterator<'a, T, iterators::log::Iter<'a, T, Self>, Self> {
        iterators::log::Iter::new(self, start, exp)
    }

    /// Iterates through all recorded histogram values using the finest granularity steps supported
    /// by the underlying representation. The iteration steps through all non-zero recorded value
    /// counts, and terminates when all recorded histogram values are exhausted.
    ///
    /// The iterator yields an `iterators::IterationValue` struct.
    ///
    /// ```
    /// use hdrsample::Histogram;
    /// use hdrsample::iterators::IterationValue;
    /// let mut hist = Histogram::<u64>::new_with_max(1000, 3).unwrap();
    /// hist += 100;
    /// hist += 500;
    /// hist += 800;
    /// hist += 850;
    ///
    /// let mut perc = hist.iter_recorded();
    /// assert_eq!(perc.next(), Some(IterationValue::new(100, hist.quantile_below(100), 1, 1)));
    /// assert_eq!(perc.next(), Some(IterationValue::new(500, hist.quantile_below(500), 1, 1)));
    /// assert_eq!(perc.next(), Some(IterationValue::new(800, hist.quantile_below(800), 1, 1)));
    /// assert_eq!(perc.next(), Some(IterationValue::new(850, hist.quantile_below(850), 1, 1)));
    /// assert_eq!(perc.next(), None);
    /// ```
    fn iter_recorded<'a>(&'a self)
            -> HistogramIterator<'a, T, iterators::recorded::Iter<'a, T, Self>, Self> {
        iterators::recorded::Iter::new(self)
    }

    /// Iterates through all histogram values using the finest granularity steps supported by the
    /// underlying representation. The iteration steps through all possible unit value levels,
    /// regardless of whether or not there were recorded values for that value level, and
    /// terminates when all recorded histogram values are exhausted.
    ///
    /// The iterator yields an `iterators::IterationValue` struct.
    ///
    /// ```
    /// use hdrsample::Histogram;
    /// use hdrsample::iterators::IterationValue;
    /// let mut hist = Histogram::<u64>::new_with_max(10, 1).unwrap();
    /// hist += 1;
    /// hist += 5;
    /// hist += 8;
    ///
    /// let mut perc = hist.iter_all();
    /// assert_eq!(perc.next(), Some(IterationValue::new(0, 0.0, 0, 0)));
    /// assert_eq!(perc.next(), Some(IterationValue::new(1, hist.quantile_below(1), 1, 1)));
    /// assert_eq!(perc.next(), Some(IterationValue::new(2, hist.quantile_below(2), 0, 0)));
    /// assert_eq!(perc.next(), Some(IterationValue::new(3, hist.quantile_below(3), 0, 0)));
    /// assert_eq!(perc.next(), Some(IterationValue::new(4, hist.quantile_below(4), 0, 0)));
    /// assert_eq!(perc.next(), Some(IterationValue::new(5, hist.quantile_below(5), 1, 1)));
    /// assert_eq!(perc.next(), Some(IterationValue::new(6, hist.quantile_below(6), 0, 0)));
    /// assert_eq!(perc.next(), Some(IterationValue::new(7, hist.quantile_below(7), 0, 0)));
    /// assert_eq!(perc.next(), Some(IterationValue::new(8, hist.quantile_below(8), 1, 1)));
    /// assert_eq!(perc.next(), Some(IterationValue::new(9, hist.quantile_below(9), 0, 0)));
    /// assert_eq!(perc.next(), Some(IterationValue::new(10, 1.0, 0, 0)));
    /// ```
    fn iter_all<'a>(&'a self) -> HistogramIterator<'a, T, iterators::all::Iter, Self> {
        iterators::all::Iter::new(self)
    }
}