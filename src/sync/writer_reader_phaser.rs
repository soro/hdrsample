//! ReaderWriterPhaser implementation used in concurrent Histograms
//!
//! Writers acquire a write interface by invoking 
//! ```let wi = WriterReaderPhaser::write(phaser)```
//! and then call 
//! ```let section_guard = wi.begin_critical_write_section()```
//! before performing an update of the data managed by the phaser.
//! Readers have to acquire a read interface via 
//! ```let ri = WriterReaderPhaser.read(phaser)```
//! and can then lock and read the data by calling 
//! ```let rg = ri.reader_lock()```
//! before finally calling `rg.flip()` once they are done executing the swap.

use std::sync::{Arc, LockResult, Mutex, MutexGuard};
use std::sync::atomic::{AtomicIsize, Ordering};
use std::isize::MIN as ISIZE_MIN;
use std::time::Duration;
use std::thread;
use std::mem;

// Struct holding all the bookkeeping variables for the phaser
pub struct WriterReaderPhaser {
    start_epoch: Arc<AtomicIsize>,
    even_end_epoch: Arc<AtomicIsize>,
    odd_end_epoch: Arc<AtomicIsize>,
    reader_lock: Arc<Mutex<PhaseFlipGuard>>
}

impl WriterReaderPhaser {
    pub fn new() -> WriterReaderPhaser {
        let start = Arc::new(AtomicIsize::new(0));
        let even_end = Arc::new(AtomicIsize::new(0));
        let odd_end = Arc::new(AtomicIsize::new(ISIZE_MIN));

        let guard = PhaseFlipGuard {
            start_epoch: start.clone(),
            even_end_epoch: even_end.clone(),
            odd_end_epoch: odd_end.clone()
        };

        WriterReaderPhaser {
            start_epoch: start,
            even_end_epoch: even_end,
            odd_end_epoch: odd_end,
            reader_lock: Arc::new(Mutex::new(guard))
        }
    }

    // To make it clear that reads and writes should be exclusive, we require acquisition of the phaser ref
    pub fn write(phaser: WriterReaderPhaser) -> PhaserWriter {
        PhaserWriter { inner: phaser }
    }

    pub fn read(phaser: WriterReaderPhaser) -> PhaserReader {
        PhaserReader { inner: phaser }
    }
}

// Write interface guarding use of the writer side methods
pub struct PhaserWriter {
    inner: WriterReaderPhaser
}

impl PhaserWriter {
    pub fn begin_writer_critical_section(&self) -> WriterCriticalSectionGuard {
        let critical_value = self.inner.start_epoch.fetch_add(1, Ordering::Release);
        if critical_value < 1 {
            WriterCriticalSectionGuard { epoch: self.inner.odd_end_epoch.clone() }
        }
        else {
            WriterCriticalSectionGuard { epoch: self.inner.even_end_epoch.clone() }
        }
    }

    pub fn end_writer_critical_section(guard: WriterCriticalSectionGuard) {
        mem::drop(guard);
    }
}

pub struct WriterCriticalSectionGuard {
    epoch: Arc<AtomicIsize>
}

impl Drop for WriterCriticalSectionGuard {
    #[allow(unused_results)] 
    fn drop(&mut self) {
        self.epoch.fetch_add(1, Ordering::Acquire);
    }
}

// Read interface guarding use of the read side methods
pub struct PhaserReader {
    inner: WriterReaderPhaser
}

impl PhaserReader {
    pub fn reader_lock(&self) -> LockResult<MutexGuard<PhaseFlipGuard>> {
        self.inner.reader_lock.lock()
    }
}

// Guard used to enforce lock before flip
pub struct PhaseFlipGuard {
    start_epoch: Arc<AtomicIsize>,
    even_end_epoch: Arc<AtomicIsize>,
    odd_end_epoch: Arc<AtomicIsize>
}

impl PhaseFlipGuard {
    pub fn flip_with_yield_time(&self, yield_time: Duration) {
        let next_phase_is_even = self.start_epoch.load(Ordering::Relaxed) < 0;

        let initial_start_value = if next_phase_is_even { 0 } else { ISIZE_MIN };
        if next_phase_is_even {
            self.even_end_epoch.store(initial_start_value, Ordering::Relaxed);
        }
        else {
            self.odd_end_epoch.store(initial_start_value, Ordering::Relaxed);
        }

        let start_value_at_flip = self.start_epoch.swap(initial_start_value, Ordering::AcqRel);

        loop {
            let caught_up = if next_phase_is_even {
                self.odd_end_epoch.load(Ordering::Relaxed) == start_value_at_flip
            }
            else {
                self.even_end_epoch.load(Ordering::Relaxed) == start_value_at_flip
            };
            if !caught_up {
                if yield_time.as_secs() == 0 && yield_time.subsec_nanos() == 0 {
                    thread::yield_now();
                }
                else {
                    thread::sleep(yield_time);
                }
            }
        }
    }

    pub fn flip(&self) {
        self.flip_with_yield_time(Duration::new(0, 0))
    }
}
