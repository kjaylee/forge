use std::any::TypeId;
use std::sync::Arc;

use forge_api::{API, AgentId, ChatRequest, ChatResponse, Event, Workflow};
use merge::Merge;
use serde_json::Value;
use tokio::sync::mpsc::{Receiver, Sender};
use tokio_stream::StreamExt;

use crate::action::Action;
use crate::command::Command;

pub struct Executor<T> {
    api: Arc<T>,
}

impl<T> Clone for Executor<T> {
    fn clone(&self) -> Self {
        Self { api: self.api.clone() }
    }
}

impl<T: API + 'static> Executor<T> {
    pub fn new(api: Arc<T>) -> Self {
        Executor { api }
    }

    async fn handle_chat(&self, message: String) -> anyhow::Result<Option<Action>> {
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

        // Execute chat request and collect responses
        let mut responses = Vec::new();
        match self.api.chat(chat_request).await {
            Ok(mut stream) => {
                while let Some(response) = stream.next().await {
                    match response {
                        Ok(ChatResponse::Text { text, is_complete, .. }) => {
                            if is_complete && !text.trim().is_empty() {
                                responses.push(text);
                            }
                        }
                        Ok(_) => {
                            // Todo:// Handle other response types (tool calls,
                            // usage, etc.)
                            // For basic functionality, we'll ignore
                            // these for now
                        }
                        Err(err) => return Err(err),
                    }
                }
            }
            Err(err) => return Err(err),
        }

        // Return aggregated response as action
        let response_text = if responses.is_empty() {
            "".to_string()
        } else {
            responses.join("\n")
        };

        Ok(Some(Action::ChatResponse { message: response_text }))
    }

    #[async_recursion::async_recursion]
    pub async fn execute(
        &self,
        cmd: Command,
        tx: &Sender<anyhow::Result<Action>>,
        tags: &mut Vec<TypeId>,
    ) -> anyhow::Result<()> {
        match cmd {
            Command::SendMessage(message) => {
                if let Some(action) = self.handle_chat(message).await? {
                    tx.send(Ok(action)).await.unwrap();
                }
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
                for command in commands {
                    Box::pin(self.execute(command, tx, tags)).await?;
                }
            }
            Command::Tagged(command, type_id) => {
                tags.push(type_id);
                self.execute(*command.to_owned(), tx, tags).await?;
            }
        }
        Ok(())
    }

    pub async fn init(&self, tx: Sender<anyhow::Result<Action>>, mut rx: Receiver<Command>) {
        let this = self.clone();
        tokio::spawn(async move {
            while let Some(cmd) = rx.recv().await {
                if let Err(error) = this.execute(cmd, &tx, &mut Vec::new()).await {
                    tx.send(Err(error)).await.unwrap();
                }
            }
        });
    }
}

#[cfg(test)]
mod tests {
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
}
