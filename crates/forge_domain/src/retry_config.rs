use derive_setters::Setters;
use merge::Merge;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize, Merge, Setters, PartialEq)]
#[setters(into)]
pub struct RetryConfig {
    /// Initial backoff delay in milliseconds for retry operations
    #[merge(strategy = crate::merge::std::overwrite)]
    pub initial_backoff_ms: u64,

    /// Backoff multiplication factor for each retry attempt
    #[merge(strategy = crate::merge::std::overwrite)]
    pub backoff_factor: u64,

    /// Maximum number of retry attempts
    #[merge(strategy = crate::merge::std::overwrite)]
    pub max_retry_attempts: usize,

    /// HTTP status codes that should trigger retries (e.g., 429, 500, 502, 503,
    /// 504)
    #[merge(strategy = crate::merge::std::overwrite)]
    pub retry_status_codes: Vec<u16>,
}
