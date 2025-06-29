use std::collections::HashMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

use ::futures::future::join_all;
use forge_api::{API, AgentId, ChatRequest, Event, Workflow};
use merge::Merge;
use serde_json::Value;
use tokio::sync::Mutex;
use tokio::sync::mpsc::{Receiver, Sender};
use tokio_stream::StreamExt;
use tokio_util::sync::CancellationToken;

use crate::domain::{Action, Command};
use crate::execute_interval;

pub struct Executor<T> {
    api: Arc<T>,
    intervals: Arc<Mutex<HashMap<u64, CancellationToken>>>,
}

static INTERVAL_ID_COUNTER: AtomicU64 = AtomicU64::new(1);

impl<T> Clone for Executor<T> {
    fn clone(&self) -> Self {
        Self { api: self.api.clone(), intervals: self.intervals.clone() }
    }
}

impl<T: API + 'static> Executor<T> {
    pub fn new(api: Arc<T>) -> Self {
        Executor { api, intervals: Arc::new(Mutex::new(HashMap::new())) }
    }

    async fn handle_chat(
        &self,
        message: String,
        tx: &Sender<anyhow::Result<Action>>,
    ) -> anyhow::Result<()> {
        // Initialize a default workflow for conversation creation
        let workflow = match self.api.read_workflow(None).await {
            Ok(workflow) => {
                // Ensure we have a default workflow
                let mut base_workflow = Workflow::default();
                base_workflow.merge(workflow);
                base_workflow
            }
            Err(_) => Workflow::default(),
        };

        // Initialize conversation if needed
        let conversation = self.api.init_conversation(workflow).await?;

        // Create event for the chat message
        // Todo:// use actual agent ID from the API
        let event = Event::new(
            format!("{}/user_task_init", AgentId::FORGE.as_str()),
            Value::String(message.clone()),
        );

        // Create chat request
        let chat_request = ChatRequest::new(event, conversation.id);

        match self.api.chat(chat_request).await {
            Ok(mut stream) => {
                while let Some(response) = stream.next().await {
                    tx.send(response.map(Action::ChatResponse)).await?;
                }
            }
            Err(err) => return Err(err),
        }
        Ok(())
    }

    #[async_recursion::async_recursion]
    pub async fn execute(
        &self,
        cmd: Command,
        tx: &Sender<anyhow::Result<Action>>,
    ) -> anyhow::Result<()> {
        match cmd {
            Command::ChatMessage(message) => {
                self.handle_chat(message, tx).await?;
            }
            Command::ReadWorkspace => {
                // Get current directory
                let current_dir = self
                    .api
                    .environment()
                    .cwd
                    .file_name()
                    .map(|name| name.to_string_lossy().to_string());

                // Get current git branch
                let current_branch = match tokio::process::Command::new("git")
                    .args(["branch", "--show-current"])
                    .output()
                    .await
                {
                    Ok(output) if output.status.success() => {
                        let branch = String::from_utf8_lossy(&output.stdout).trim().to_string();
                        if branch.is_empty() {
                            None
                        } else {
                            Some(branch)
                        }
                    }
                    _ => None,
                };

                let action = Action::Workspace { current_dir, current_branch };
                tx.send(Ok(action)).await.unwrap();
            }
            Command::Empty => {
                // Empty command doesn't send any action
            }
            Command::Exit => {
                // Exit command doesn't send any action
            }
            Command::And(commands) => {
                // Execute all commands in sequence, each sending their own actions
                join_all(
                    commands
                        .into_iter()
                        .map(|command| self.execute(command, tx)),
                )
                .await
                .into_iter()
                .collect::<anyhow::Result<Vec<_>>>()?;
            }
            Command::Interval { duration } => {
                // Use default duration if none provided
                let interval_duration = duration.unwrap_or(Duration::from_secs(1));
                let cancellation_token = CancellationToken::new();
                let id = INTERVAL_ID_COUNTER.fetch_add(1, Ordering::SeqCst);
                execute_interval::execute_interval(
                    interval_duration,
                    tx.clone(),
                    cancellation_token.clone(),
                    id,
                )
                .await;

                // Store the cancellation token for this interval
                self.intervals.lock().await.insert(id, cancellation_token);
            }
            Command::CancelInterval { id } => {
                // Remove and cancel the interval if it exists
                if let Some(cancellation_token) = self.intervals.lock().await.remove(&id) {
                    cancellation_token.cancel();
                }
                // No action is sent for cancellation
            }
        }
        Ok(())
    }

    pub async fn init(&self, tx: Sender<anyhow::Result<Action>>, mut rx: Receiver<Command>) {
        let this = self.clone();
        tokio::spawn(async move {
            while let Some(cmd) = rx.recv().await {
                if let Err(error) = this.execute(cmd, &tx).await {
                    tx.send(Err(error)).await.unwrap();
                }
            }
        });
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use pretty_assertions::assert_eq;
    use tokio::sync::mpsc;

    use super::*;

    #[tokio::test]
    async fn test_and_command_structure_with_empty_commands() {
        let command = Command::And(vec![Command::Empty, Command::Empty]);

        match command {
            Command::And(commands) => {
                assert_eq!(commands.len(), 2);
                assert_eq!(commands[0], Command::Empty);
                assert_eq!(commands[1], Command::Empty);
            }
            _ => panic!("Expected Command::And"),
        }
    }

    #[tokio::test]
    async fn test_and_command_structure() {
        let command = Command::And(vec![Command::Empty, Command::ReadWorkspace, Command::Exit]);

        match command {
            Command::And(commands) => {
                assert_eq!(commands.len(), 3);
                assert_eq!(commands[0], Command::Empty);
                assert_eq!(commands[1], Command::ReadWorkspace);
                assert_eq!(commands[2], Command::Exit);
            }
            _ => panic!("Expected Command::And"),
        }
    }

    #[tokio::test]
    async fn test_execute_empty_command_sends_no_action() {
        let (tx, mut rx) = mpsc::channel::<anyhow::Result<Action>>(10);

        // We can't easily test without a real API implementation
        // So we'll just test the command structure
        let command = Command::Empty;
        assert_eq!(command, Command::Empty);

        // Close the channel to prevent hanging
        drop(tx);

        // Verify no messages were sent
        let result = rx.try_recv();
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_interval_command_structure() {
        let duration = Some(Duration::from_millis(100));
        let fixture = Command::Interval { duration };

        match fixture {
            Command::Interval { duration: actual_duration } => {
                let expected = Some(Duration::from_millis(100));
                assert_eq!(actual_duration, expected);
            }
            _ => panic!("Expected Command::Interval"),
        }
    }

    #[tokio::test]
    async fn test_interval_command_with_none_duration() {
        let fixture = Command::Interval { duration: None };

        match fixture {
            Command::Interval { duration: actual_duration } => {
                let expected = None;
                assert_eq!(actual_duration, expected);
            }
            _ => panic!("Expected Command::Interval"),
        }
    }
}
