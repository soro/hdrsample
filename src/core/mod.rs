//! core components and types used throughout this library

/// Settings common to all histogram types. 
pub mod histogram_settings;
pub use self::histogram_settings::*;

/// Error types used throughout this library.
pub mod errors;
pub use self::errors::*;

/// Counter type defining operations required by the histogram and impls for primitives.
pub mod counter;
pub use self::counter::*;

pub mod histogram;
pub use self::histogram::*;

pub mod histogram_interface;
pub use self::histogram_interface::*;