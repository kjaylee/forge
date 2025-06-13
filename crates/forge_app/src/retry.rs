use std::future::Future;
use std::time::Duration;

use anyhow::Context;
use backon::{ExponentialBuilder, Retryable};
use forge_domain::{Error, RetryConfig};

/// Retry wrapper for operations that may fail with retryable errors
pub async fn retry_with_config<T, FutureFn, Fut>(
    config: &RetryConfig,
    operation: FutureFn,
) -> anyhow::Result<T>
where
    FutureFn: FnMut() -> Fut,
    Fut: Future<Output = anyhow::Result<T>>,
{
    let strategy = ExponentialBuilder::default()
        .with_min_delay(Duration::from_millis(config.min_delay_ms))
        .with_factor(config.backoff_factor as f32)
        .with_max_times(config.max_retry_attempts)
        .with_jitter();

    operation
        .retry(strategy)
        .when(should_retry)
        .await
        .with_context(|| "Failed to execute operation with retry")
}

/// Determines if an error should trigger a retry attempt.
///
/// This function checks if the error is a retryable domain error.
/// Currently, only `Error::Retryable` errors will trigger retries.
fn should_retry(error: &anyhow::Error) -> bool {
    error
        .downcast_ref::<Error>()
        .is_some_and(|error| matches!(error, Error::Retryable(_, _)))
}

#[cfg(test)]
mod tests {
    use std::sync::{Arc, Mutex};

    use pretty_assertions::assert_eq;

    use super::*;

    #[tokio::test]
    async fn test_retry_success_on_first_attempt() {
        // Fixture: Create retry config and successful operation
        let retry_config = RetryConfig::default().min_delay_ms(0u64);
        let call_count = Arc::new(Mutex::new(0));
        let call_count_clone = call_count.clone();

        // Actual: Execute operation that succeeds immediately
        let actual = retry_with_config(&retry_config, || {
            let call_count_clone = call_count_clone.clone();
            async move {
                {
                    let mut count = call_count_clone.lock().unwrap();
                    *count += 1;
                }
                Ok::<i32, anyhow::Error>(42)
            }
        })
        .await;

        // Expected: Should succeed on first try
        assert!(actual.is_ok());
        assert_eq!(actual.unwrap(), 42);
        assert_eq!(*call_count.lock().unwrap(), 1);
    }

    #[tokio::test]
    async fn test_retry_with_retryable_error_eventually_succeeds() {
        // Fixture: Create retry config and operation that fails then succeeds
        let retry_config = RetryConfig::default()
            .max_retry_attempts(3usize)
            .initial_backoff_ms(1u64)
            .min_delay_ms(1u64)
            .backoff_factor(1u64);
        let call_count = Arc::new(Mutex::new(0));
        let call_count_clone = call_count.clone();

        // Actual: Execute operation that fails twice then succeeds
        let actual = retry_with_config(&retry_config, || {
            let call_count_clone = call_count_clone.clone();
            async move {
                let count = {
                    let mut count = call_count_clone.lock().unwrap();
                    *count += 1;
                    *count
                };
                if count <= 2 {
                    Err(anyhow::anyhow!(Error::Retryable(
                        3,
                        anyhow::anyhow!("Test retryable error")
                    )))
                } else {
                    Ok::<i32, anyhow::Error>(42)
                }
            }
        })
        .await;

        // Expected: Should succeed after retries
        assert!(actual.is_ok());
        assert_eq!(actual.unwrap(), 42);
        assert_eq!(*call_count.lock().unwrap(), 3);
    }

    #[tokio::test]
    async fn test_retry_with_retryable_error_exceeds_max_attempts() {
        // Fixture: Create retry config and operation that always fails
        let retry_config = RetryConfig::default()
            .max_retry_attempts(2usize)
            .initial_backoff_ms(1u64)
            .min_delay_ms(1u64)
            .backoff_factor(1u64);
        let call_count = Arc::new(Mutex::new(0));
        let call_count_clone = call_count.clone();

        // Actual: Execute operation that always fails
        let actual = retry_with_config(&retry_config, || {
            let call_count_clone = call_count_clone.clone();
            async move {
                {
                    let mut count = call_count_clone.lock().unwrap();
                    *count += 1;
                }
                Err::<i32, anyhow::Error>(anyhow::anyhow!(Error::Retryable(
                    2,
                    anyhow::anyhow!("Test retryable error")
                )))
            }
        })
        .await;

        // Expected: Should fail after max attempts
        assert!(actual.is_err());
        assert_eq!(*call_count.lock().unwrap(), 3); // 1 initial + 2 retries
    }

    #[tokio::test]
    async fn test_retry_with_non_retryable_error() {
        // Fixture: Create retry config and operation that fails with non-retryable
        // error
        let retry_config = RetryConfig::default().min_delay_ms(0u64);
        let call_count = Arc::new(Mutex::new(0));
        let call_count_clone = call_count.clone();

        // Actual: Execute operation that fails with non-retryable error
        let actual = retry_with_config(&retry_config, || {
            let call_count_clone = call_count_clone.clone();
            async move {
                {
                    let mut count = call_count_clone.lock().unwrap();
                    *count += 1;
                }
                Err::<i32, anyhow::Error>(anyhow::anyhow!("Non-retryable error"))
            }
        })
        .await;

        // Expected: Should fail immediately without retries
        assert!(actual.is_err());
        assert_eq!(*call_count.lock().unwrap(), 1);
    }

    #[tokio::test]
    async fn test_retry_config_ext_trait() {
        // Fixture: Create retry config and use extension trait
        let retry_config = RetryConfig::default().min_delay_ms(0u64);
        let call_count = Arc::new(Mutex::new(0));
        let call_count_clone = call_count.clone();

        // Actual: Execute operation using extension trait
        let actual = retry_with_config(&retry_config, || {
            let call_count_clone = call_count_clone.clone();
            async move {
                {
                    let mut count = call_count_clone.lock().unwrap();
                    *count += 1;
                }
                Ok::<i32, anyhow::Error>(42)
            }
        })
        .await;

        // Expected: Should succeed
        assert!(actual.is_ok());
        assert_eq!(actual.unwrap(), 42);
        assert_eq!(*call_count.lock().unwrap(), 1);
    }

    #[test]
    fn test_should_retry_with_retryable_error() {
        // Fixture: Create retryable error
        let retryable_error =
            anyhow::anyhow!(Error::Retryable(3, anyhow::anyhow!("Test retryable error")));

        // Actual: Check if error should be retried
        let actual = should_retry(&retryable_error);

        // Expected: Should return true
        assert_eq!(actual, true);
    }

    #[test]
    fn test_should_retry_with_non_retryable_error() {
        // Fixture: Create non-retryable error
        let non_retryable_error = anyhow::anyhow!("Non-retryable error");

        // Actual: Check if error should be retried
        let actual = should_retry(&non_retryable_error);

        // Expected: Should return false
        assert_eq!(actual, false);
    }

    #[tokio::test]
    async fn test_exponential_backoff_calculation() {
        // Fixture: Create retry config with exponential backoff
        let retry_config = RetryConfig::default()
            .max_retry_attempts(2usize)
            .initial_backoff_ms(10u64)
            .min_delay_ms(10u64)
            .backoff_factor(2u64);
        let call_count = Arc::new(Mutex::new(0));
        let call_count_clone = call_count.clone();
        let start_time = std::time::Instant::now();

        // Actual: Execute operation that fails multiple times
        let _actual = retry_with_config(&retry_config, || {
            let call_count_clone = call_count_clone.clone();
            async move {
                {
                    let mut count = call_count_clone.lock().unwrap();
                    *count += 1;
                }
                Err::<i32, anyhow::Error>(anyhow::anyhow!(Error::Retryable(
                    2,
                    anyhow::anyhow!("Test retryable error")
                )))
            }
        })
        .await;

        let elapsed = start_time.elapsed();

        // Expected: Should have taken some time due to exponential backoff
        // First delay: 10ms, Second delay: 20ms = at least 30ms total
        assert!(elapsed >= Duration::from_millis(25)); // Allow some tolerance
        assert_eq!(*call_count.lock().unwrap(), 3); // 1 initial + 2 retries
    }
}
