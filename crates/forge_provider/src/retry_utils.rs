use std::time::Duration;

use anyhow::Error;
use forge_domain::RetryConfig;
use tokio_retry::strategy::{jitter, ExponentialBackoff};
use tokio_retry::RetryIf;
use tracing::debug;

use crate::utils::is_tls_handshake_eof;

/// A utility struct for handling retries with configurable conditions
pub struct RetryHandler {
    /// The retry configuration
    config: RetryConfig,
}

impl RetryHandler {
    /// Create a new RetryHandler with the given configuration
    pub fn new(config: RetryConfig) -> Self {
        Self { config }
    }

    /// Execute an async operation with retry logic
    pub async fn retry<F, Fut, T>(&self, operation: F) -> Result<T, Error>
    where
        F: FnMut() -> Fut,
        Fut: std::future::Future<Output = Result<T, Error>>,
    {
        // Create a retry strategy using the configured retry_config
        let retry_strategy = ExponentialBackoff::from_millis(self.config.initial_backoff_ms)
            .factor(self.config.backoff_factor)
            .max_delay(Duration::from_secs(10))
            .map(jitter)
            .take(self.config.max_retry_attempts);

        // Clone retry_status_codes for use in the condition closure
        let retry_status_codes = self.config.retry_status_codes.clone();

        // Create a retry condition that checks for specific HTTP status codes
        let condition = move |err: &Error| {
            // Check if the error contains a status code that should be retried
            let should_retry = err.chain().any(|cause| {
                // Check for HTTP status codes that should be retried
                if let Some(reqwest_err) = cause.downcast_ref::<reqwest::Error>() {
                    if let Some(status) = reqwest_err.status() {
                        if retry_status_codes.contains(&status.as_u16()) {
                            debug!(status = %status, "Retrying due to status code");
                            return true;
                        }
                    }

                    // Retry on network errors (like TLS handshake EOF)
                    if reqwest_err.is_connect()
                        || reqwest_err.is_timeout()
                        || is_tls_handshake_eof(reqwest_err)
                    {
                        debug!("Retrying due to network error");
                        return true;
                    }
                }

                false
            });

            should_retry
        };

        // Execute with retry and condition
        RetryIf::spawn(retry_strategy, operation, condition).await
    }
}
