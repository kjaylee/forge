use std::time::Duration;

use anyhow::Error;
use forge_domain::RetryConfig;
use reqwest_eventsource::retry::RetryPolicy;
use reqwest_eventsource::Error as EventSourceError;
use tokio_retry::strategy::{jitter, ExponentialBackoff};
use tokio_retry::RetryIf;
use tracing::debug;

use crate::utils::is_tls_handshake_eof;

/// A RetryPolicy that only retries on specific status codes
pub struct StatusCodeRetryPolicy {
    /// The inner backoff policy
    inner: reqwest_eventsource::retry::ExponentialBackoff,
    /// Retry configuration
    retry_config: RetryConfig,
}

impl StatusCodeRetryPolicy {
    /// Create a new status code specific retry policy
    pub fn new(retry_config: RetryConfig) -> Self {
        Self {
            inner: reqwest_eventsource::retry::ExponentialBackoff::new(
                Duration::from_millis(retry_config.initial_backoff_ms),
                retry_config.backoff_factor as f64,
                None,
                Some(retry_config.max_retry_attempts),
            ),
            retry_config,
        }
    }

    /// Execute an async operation with retry logic
    pub async fn retry_with_fn<F, Fut, T>(&self, operation: F) -> Result<T, Error>
    where
        F: FnMut() -> Fut,
        Fut: std::future::Future<Output = Result<T, Error>>,
    {
        // Create a retry strategy using the configured retry_config
        let retry_strategy = ExponentialBackoff::from_millis(self.retry_config.initial_backoff_ms)
            .factor(self.retry_config.backoff_factor)
            .max_delay(Duration::from_secs(10))
            .map(jitter)
            .take(self.retry_config.max_retry_attempts);

        // Clone retry_status_codes for use in the condition closure
        let retry_status_codes = self.retry_config.retry_status_codes.clone();

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

impl RetryPolicy for StatusCodeRetryPolicy {
    fn retry(
        &self,
        error: &EventSourceError,
        last_retry: Option<(usize, Duration)>,
    ) -> Option<Duration> {
        // Only retry for specific status codes
        match error {
            EventSourceError::InvalidStatusCode(status_code, _) => {
                // Check if the status code is in our retry list
                if self
                    .retry_config
                    .retry_status_codes
                    .contains(&status_code.as_u16())
                {
                    // Delegate to inner policy for backoff calculation
                    self.inner.retry(error, last_retry)
                } else {
                    // Don't retry for status codes not in our list
                    None
                }
            }
            // For network/transport errors, always retry
            EventSourceError::Transport(_) => self.inner.retry(error, last_retry),
            // Don't retry for other types of errors
            _ => None,
        }
    }

    fn set_reconnection_time(&mut self, duration: Duration) {
        self.inner.set_reconnection_time(duration)
    }
}
