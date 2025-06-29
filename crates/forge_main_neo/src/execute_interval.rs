use std::time::Duration;

use chrono::Utc;
use tokio::sync::mpsc::Sender;
use tokio::time::interval;
use tokio_util::sync::CancellationToken;

use crate::domain::{Action, Timer};

/// Execute an interval command that emits IntervalTick actions at regular
/// intervals
///
/// This function creates a background task that sends IntervalTick actions at
/// the specified duration. The task will continue until the sender is dropped
/// or the cancellation token is triggered, ensuring no memory leaks.
///
/// # Arguments
/// * `duration` - The interval duration between ticks
/// * `tx` - Channel sender for emitting actions
/// * `cancellation_token` - Token to cancel the interval
///
/// # Returns
/// * `u64` - The unique ID assigned to this interval
pub async fn execute_interval(
    duration: Duration,
    tx: Sender<anyhow::Result<Action>>,
    cancellation_token: CancellationToken,
    id: u64,
) {
    let start_time = Utc::now();

    // Create a tokio interval timer
    let mut interval_timer = interval(duration);

    // Skip the first tick which fires immediately
    interval_timer.tick().await;

    // Spawn a background task to handle the interval

    loop {
        tokio::select! {
            _ = interval_timer.tick() => {
                let current_time = Utc::now();
                let action = Action::IntervalTick(Timer{start_time, current_time, duration, id });

                // Send the action, if the receiver is dropped, break the loop
                if tx.send(Ok(action)).await.is_err() {
                    // Channel closed, exit the loop to prevent memory leaks
                    break;
                }
            }
            _ = cancellation_token.cancelled() => {
                // Interval was cancelled, exit cleanly
                break;
            }
        }
    }
}
