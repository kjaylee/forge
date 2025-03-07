#[cfg(test)]
mod tests {
    use crate::{init_tracing_with_posthog, Tracker, EventKind};
    use tracing::{info, debug, warn, error};

    #[tokio::test]
    async fn test_posthog_logging() {
        let tracker = Box::leak(Box::new(Tracker::default()));
        
        // Create a temporary directory for logs
        let log_path = std::env::temp_dir();
        
        // Initialize tracing with PostHog integration
        let _guard = init_tracing_with_posthog(log_path, tracker).unwrap();
        
        // Generate some log events at different levels
        debug!("This is a debug message");
        info!("This is an info message");
        warn!("This is a warning message with data: {}", 42);
        error!("This is an error message: {}", "test error");
        
        // Manually dispatch an event
        let _ = tracker.dispatch(EventKind::Prompt("test prompt".to_string())).await;
        
        // Sleep briefly to allow async processing
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        
        // We can't easily assert on PostHog events in tests, but this ensures the code paths are exercised
    }
}