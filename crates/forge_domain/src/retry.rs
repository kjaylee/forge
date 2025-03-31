use std::sync::Arc;

use tokio_retry::RetryIf;

use crate::{Agent, AgentMessage, ChatResponse, Error};

type ArcSender = Arc<tokio::sync::mpsc::Sender<anyhow::Result<AgentMessage<ChatResponse>>>>;

/// Parameters for checking and logging retry conditions
#[derive(Debug, Clone)]
pub struct RetryCondition<'a> {
    pub err: &'a anyhow::Error,
    pub attempt: usize,
    pub max_attempts: usize,
    pub agent: Option<&'a Agent>,
    pub sender: Option<&'a ArcSender>,
}

impl<'a> RetryCondition<'a> {
    /// Creates a new RetryCondition instance
    pub fn new(
        err: &'a anyhow::Error,
        attempt: usize,
        max_attempts: usize,
        agent: Option<&'a Agent>,
        sender: Option<&'a ArcSender>,
    ) -> Self {
        Self { err, attempt, max_attempts, agent, sender }
    }

    /// Checks if an error is retriable based on domain error types
    pub fn is_retriable(&self) -> bool {
        if let Some(domain_err) = self.err.downcast_ref::<Error>() {
            matches!(
                domain_err,
                Error::ToolCallParse(_) | Error::ToolCallArgument(_) | Error::ToolCallMissingName
            ) && self.attempt < self.max_attempts
        } else {
            false
        }
    }

    /// Checks if an error is retriable and sends a retry event if needed
    pub async fn check_and_log_retry_condition(&self) -> bool {
        let is_retriable = self.is_retriable();
        if let (true, Some(a), Some(s)) = (is_retriable, self.agent, self.sender) {
            let _ = s
                .send(Ok(AgentMessage {
                    agent: a.id.clone(),
                    message: ChatResponse::Retry {
                        reason: format!("{}", self.err),
                        attempt: self.attempt,
                        max_attempts: self.max_attempts,
                    },
                }))
                .await;
        }
        is_retriable
    }
}

/// Executes an operation with retry logic based on specified conditions
///
/// # Arguments
///
/// * `agent` - The agent for which the operation is being executed
/// * `sender` - The message sender for notifications
/// * `retry_strategy` - The retry strategy to use (e.g., exponential backoff)
/// * `operation` - The async operation to retry
/// * `max_attempts` - Maximum number of retry attempts
/// * `context` - A function that provides context for error messages
///
/// # Returns
///
/// The result of the operation, or an error if all retry attempts failed
pub async fn execute_with_retry<T, F, Fut>(
    agent: &Agent,
    sender: Option<&ArcSender>,
    retry_strategy: impl IntoIterator<Item = std::time::Duration> + Clone,
    operation: F,
    max_attempts: usize,
) -> anyhow::Result<T>
where
    F: FnMut() -> Fut,
    Fut: std::future::Future<Output = anyhow::Result<T>>,
{
    let mut attempt = 0;

    let result = RetryIf::spawn(retry_strategy, operation, move |err: &anyhow::Error| {
        attempt += 1;
        RetryCondition::new(err, attempt, max_attempts, None, None).is_retriable()
    })
    .await;

    // Handle error notifications and logging
    if let Err(ref err) = result {
        RetryCondition::new(err, attempt, max_attempts, Some(agent), sender)
            .check_and_log_retry_condition()
            .await;
    }

    result
}
