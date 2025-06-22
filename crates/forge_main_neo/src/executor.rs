use std::sync::Arc;
use std::time::Duration;

use forge_api::API;
use tokio::sync::mpsc::{Receiver, Sender};

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

    pub async fn execute(&self, cmd: Command) -> anyhow::Result<Option<Action>> {
        match cmd {
            Command::Chat(message) => {
                tokio::time::sleep(Duration::from_millis(5000)).await;
                Ok(Some(Action::ChatResponse {
                    message: message.chars().rev().collect::<String>(),
                }))
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
