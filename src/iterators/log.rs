use core::counter::Counter;
use core::histogram::Histogram;
use iterators::{HistogramIterator, PickyIterator};
use std::marker::PhantomData;

/// An iterator that will yield at log-size steps through the histogram's value range.
pub struct Iter<'a, T: 'a + Counter, H: 'a + Histogram<T>> {
    hist: &'a H,

    // > 1.0
    next_value_reporting_level: f64,
    // > 1.0
    log_base: f64,

    current_step_lowest_value_reporting_level: u64,
    current_step_highest_value_reporting_level: u64,
    counter_phantom: PhantomData<T>
}

impl<'a, T: 'a + Counter, H: 'a + Histogram<T>> Iter<'a, T, H> {
    /// Construct a new logarithmic iterator. See `Histogram::iter_log` for details.
    pub fn new(hist: &'a H,
               value_units_in_first_bucket: u64,
               log_base: f64)
               -> HistogramIterator<'a, T, Iter<'a, T, H>, H> {
        assert!(value_units_in_first_bucket > 0, "value_units_per_bucket must be > 0");
        assert!(log_base > 1.0, "log_base must be > 1.0");
        HistogramIterator::new(hist,
                               Iter {
                                   hist: hist,
                                   log_base: log_base,
                                   next_value_reporting_level: value_units_in_first_bucket as f64,
                                   current_step_highest_value_reporting_level: value_units_in_first_bucket -
                                                                          1,
                                   current_step_lowest_value_reporting_level:
                                       hist.settings().lowest_equivalent(value_units_in_first_bucket - 1),
                                   counter_phantom: PhantomData
                               })
    }
}

impl<'a, T: 'a + Counter, H: 'a + Histogram<T>> PickyIterator<T> for Iter<'a, T, H> {
    fn pick(&mut self, index: usize, _: u64) -> bool {
        let val = self.hist.settings().value_for(index);
        if val >= self.current_step_lowest_value_reporting_level || index == self.hist.last_index() {
            // implies log_base must be > 1.0
            self.next_value_reporting_level *= self.log_base;
            // won't underflow since next_value_reporting_level starts > 0 and only grows
            self.current_step_highest_value_reporting_level = self.next_value_reporting_level as u64 - 1;
            self.current_step_lowest_value_reporting_level = self.hist.settings()
                .lowest_equivalent(self.current_step_highest_value_reporting_level);
            true
        } else {
            false
        }
    }

    fn more(&mut self, next_index: usize) -> bool {
        // If the next iterate will not move to the next sub bucket index (which is empty if if we
        // reached this point), then we are not yet done iterating (we want to iterate until we are
        // no longer on a value that has a count, rather than util we first reach the last value
        // that has a count. The difference is subtle but important)...
        self.hist.settings().lowest_equivalent(self.next_value_reporting_level as u64) <
            self.hist.settings().value_for(next_index)
    }
}
