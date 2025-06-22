use std::sync::Arc;

use forge_api::{API, AgentId, ChatRequest, ChatResponse, Event, Workflow};
use merge::Merge;
use serde_json::Value;
use tokio::sync::mpsc::{Receiver, Sender};
use tokio_stream::StreamExt;

use crate::model::{Action, Command};

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

    pub async fn execute(&self, cmd: Command) -> anyhow::Result<Option<Action>> {
        match cmd {
            Command::Chat(message) => self.handle_chat(message).await,
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

                Ok(Some(Action::Workspace { current_dir, current_branch }))
            }
            Command::Empty => Ok(None),
            Command::Exit => Ok(None),
        }
    }

    pub async fn init(&self, tx: Sender<anyhow::Result<Action>>, mut rx: Receiver<Command>) {
        let this = self.clone();
        tokio::spawn(async move {
            while let Some(cmd) = rx.recv().await {
                match this.execute(cmd).await {
                    Ok(Some(action)) => tx.send(Ok(action)).await.unwrap(),
                    Ok(None) => {}
                    Err(error) => tx.send(Err(error)).await.unwrap(),
                }
            }
        });
    }
}
