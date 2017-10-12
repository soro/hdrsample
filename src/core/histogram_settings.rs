use core::errors::*;

const ORIGINAL_MIN: u64 = (-1_i64 >> 63) as u64;
/// Max value of a new histogram.
const ORIGINAL_MAX: u64 = 0;

#[allow(dead_code)] 
#[derive(Debug)]
pub struct HistogramSettings {
    pub auto_resize: bool,

    // >= 2 * lowest_discernible_value
    pub highest_trackable_value: u64,
    // >= 1
    pub lowest_discernible_value: u64,
    // in [0, 5]
    pub significant_value_digits: u8,

    //counts_array_length: usize,

    // in [1, 64]
    pub bucket_count: u8,
    // 2^(sub_bucket_half_count_magnitude + 1) = [2, 2^18]
    pub sub_bucket_count: u32,
    // sub_bucket_count / 2 = [1, 2^17]
    pub sub_bucket_half_count: u32,
    // In [0, 17]
    pub sub_bucket_half_count_magnitude: u8,
    // The bottom sub bucket's bits set, shifted by unit magnitude.
    // The highest bit will be (one-indexed) sub bucket count magnitude + unit_magnitude.
    pub sub_bucket_mask: u64,

    // Number of leading zeros that would be used by the largest value in bucket 0.
    // in [1, 63]
    pub leading_zero_count_base: u8,

    // Largest exponent of 2 that's smaller than the lowest discernible value. In [0, 62].
    pub unit_magnitude: u8,
    // low unit_magnitude bits set
    pub unit_magnitude_mask: u64,

    pub max_value: u64,
    pub min_non_zero_value: u64
}

#[allow(dead_code)] 
impl HistogramSettings {
    /// Construct a `Histogram` with known upper and lower bounds for recorded sample values.
    ///
    /// `low` is the lowest value that can be discerned (distinguished from 0) by the histogram,
    /// and must be a positive integer that is >= 1. It may be internally rounded down to nearest
    /// power of 2. Providing a lowest discernible value (`low`) is useful is situations where the
    /// units used for the histogram's values are much smaller that the minimal accuracy required.
    /// E.g. when tracking time values stated in nanosecond units, where the minimal accuracy
    /// required is a microsecond, the proper value for `low` would be 1000. If you're not sure,
    /// use 1.
    ///
    /// `high` is the highest value to be tracked by the histogram, and must be a
    /// positive integer that is `>= (2 * low)`. If you're not sure, use `u64::max_value()`.
    ///
    /// `sigfig` Specifies the number of significant figures to maintain. This is the number of
    /// significant decimal digits to which the histogram will maintain value resolution and
    /// separation. Must be in the range [0, 5]. If you're not sure, use 3. As `sigfig` increases,
    /// memory usage grows exponentially, so choose carefully if there will be many histograms in
    /// memory at once or if storage is otherwise a concern.
    ///
    /// Returns an error if the provided parameters are invalid; see `CreationError`.
    fn new_with_bounds(low: u64, high: u64, sigfig: u8) -> Result<HistogramSettings, CreationError> {
        // Verify argument validity
        if low < 1 {
            return Err(CreationError::LowIsZero);
        }
        if low > u64::max_value() / 2 {
            // avoid overflow in 2 * low
            return Err(CreationError::LowExceedsMax)
        }
        if high < 2 * low {
            return Err(CreationError::HighLessThanTwiceLow);
        }
        if sigfig > 5 {
            return Err(CreationError::SigFigExceedsMax);
        }

        // Given a 3 decimal point accuracy, the expectation is obviously for "+/- 1 unit at 1000".
        // It also means that it's "ok to be +/- 2 units at 2000". The "tricky" thing is that it is
        // NOT ok to be +/- 2 units at 1999. Only starting at 2000. So internally, we need to
        // maintain single unit resolution to 2x 10^decimal_points.

        // largest value with single unit resolution, in [2, 200_000].
        let largest = 2 * 10_u32.pow(sigfig as u32);

        let unit_magnitude = (low as f64).log2().floor() as u8;
        let unit_magnitude_mask = (1 << unit_magnitude) - 1;

        // We need to maintain power-of-two sub_bucket_count (for clean direct indexing) that is
        // large enough to provide unit resolution to at least
        // largest_value_with_single_unit_resolution. So figure out
        // largest_value_with_single_unit_resolution's nearest power-of-two (rounded up), and use
        // that.
        // In [1, 18]. 2^18 > 2 * 10^5 (the largest possible
        // largest_value_with_single_unit_resolution)
        let sub_bucket_count_magnitude = (largest as f64).log2().ceil() as u8;
        let sub_bucket_half_count_magnitude = sub_bucket_count_magnitude - 1;
        let sub_bucket_count = 1_u32 << (sub_bucket_count_magnitude as u32);

        if unit_magnitude + sub_bucket_count_magnitude > 63 {
            // sub_bucket_count entries can't be represented, with unit_magnitude applied, in a
            // u64. Technically it still sort of works if their sum is 64: you can represent all
            // but the last number in the shifted sub_bucket_count. However, the utility of such a
            // histogram vs ones whose magnitude here fits in 63 bits is debatable, and it makes
            // it harder to work through the logic. Sums larger than 64 are totally broken as
            // leading_zero_count_base would go negative.
            return Err(CreationError::CannotRepresentSigFigBeyondLow);
        };

        let sub_bucket_half_count = sub_bucket_count / 2;
        // sub_bucket_count is always at least 2, so subtraction won't underflow
        let sub_bucket_mask = (sub_bucket_count as u64 - 1) << unit_magnitude;

        let mut s = HistogramSettings {
            auto_resize: false,

            highest_trackable_value: high,
            lowest_discernible_value: low,
            significant_value_digits: sigfig,

            // set by resize() below
            bucket_count: 0,
            sub_bucket_count,


            // Establish leading_zero_count_base, used in bucket_index_of() fast path:
            // subtract the bits that would be used by the largest value in bucket 0.
            leading_zero_count_base: 64 - unit_magnitude - sub_bucket_count_magnitude,
            sub_bucket_half_count_magnitude,

            unit_magnitude,
            sub_bucket_half_count,

            sub_bucket_mask,

            unit_magnitude_mask,
            max_value: ORIGINAL_MAX,
            min_non_zero_value: ORIGINAL_MIN,
        };

        Ok(s)
    }
}