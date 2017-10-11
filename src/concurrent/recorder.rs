
use std::sync::atomic::{AtomicUsize, Ordering};
use concurrent::writer_reader_phaser::WriterReaderPhaser;
//use super::super::{Histogram, Counter};

static REPORTER_INSTANCE_SEQUENCER: AtomicUsize = AtomicUsize::new(0);

pub struct Recorder {
    pub instance_id: usize,
    pub recording_phaser: WriterReaderPhaser,
    //active_histogram: Histogram<T>,
    //inactive_histogram: Histogram<T>
}

impl Recorder {
    pub fn new() -> Recorder {
        let id = REPORTER_INSTANCE_SEQUENCER.fetch_add(1, Ordering::SeqCst);
        let phaser = WriterReaderPhaser::new();
        Recorder { instance_id: id, recording_phaser: phaser }
    }
}