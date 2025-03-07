mod can_track;
mod collect;
mod dispatch;
mod error;
mod event;
mod log;
mod log_posthog;
#[cfg(test)]
mod log_posthog_tests;
pub use can_track::VERSION;
pub use dispatch::Tracker;
use error::Result;
pub use event::{Event, EventKind};
pub use log::{init_tracing, init_tracing_with_posthog, Guard};
pub use log_posthog::PosthogLayer;
