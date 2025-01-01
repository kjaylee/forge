use std::sync::Arc;

use forge_env::Environment;
use forge_provider::{BoxStream, Provider, Request, Response, ResultStream, ToolResult};
use forge_tool::ToolEngine;
use tokio::sync::mpsc;
use tokio_stream::StreamExt;

use crate::app::{Action, ChatResponse, Command, FileResponse};
use crate::runtime::Executor;
use crate::system_prompt::SystemPrompt;
use crate::Error;

pub struct ChatCommandExecutor {
    provider: Arc<Provider<Request, Response, forge_provider::Error>>,
    tools: Arc<ToolEngine>,
    tx: mpsc::Sender<ChatResponse>,
    system_prompt: SystemPrompt,
}

impl ChatCommandExecutor {
    pub fn new(
        env: Environment,
        api_key: impl Into<String>,
        tx: mpsc::Sender<ChatResponse>,
    ) -> Self {
        let tools = Arc::new(ToolEngine::new());

        Self {
            provider: Arc::new(Provider::open_router(api_key.into(), None)),
            tools: tools.clone(),
            tx,
            system_prompt: SystemPrompt::new(env, tools),
        }
    }
}

#[async_trait::async_trait]
impl Executor for ChatCommandExecutor {
    type Command = Command;
    type Action = Action;
    type Error = Error;
    async fn execute(&self, command: &Self::Command) -> ResultStream<Self::Action, Self::Error> {
        match command {
            Command::FileRead(files) => {
                let mut responses = vec![];
                for file in files {
                    match tokio::fs::read_to_string(file.clone()).await {
                        Ok(content) => {
                            responses.push(FileResponse { path: file.to_string(), content });
                        }
                        Err(e) => {
                            // Send error through the channel before returning empty stream
                            let _ = self.tx.send(ChatResponse::Fail(format!("Failed to read file {}: {}", file, e))).await;
                            return Ok(Box::pin(tokio_stream::empty()));
                        }
                    }
                }

                let stream: BoxStream<Action, Error> =
                    Box::pin(tokio_stream::once(Ok(Action::FileReadResponse(responses))));

                Ok(stream)
            }
            Command::AssistantMessage(request) => {
                // TODO: To use or not to use tools should be decided by the app and not the
                // executor. Set system prompt based on the model type
                let parameters = match self.provider.parameters(request.model.clone()).await {
                    Ok(params) => params,
                    Err(e) => {
                        // Send error through the channel before returning empty stream
                        let _ = self.tx.send(ChatResponse::Fail(e.to_string())).await;
                        return Ok(Box::pin(tokio_stream::empty()));
                    }
                };
                let request = if parameters.tools {
                    request
                        .clone()
                        .set_system_message(match self.system_prompt.clone().use_tool(true).render() {
                            Ok(msg) => msg,
                            Err(e) => {
                                // Send error through the channel before returning empty stream
                                let _ = self.tx.send(ChatResponse::Fail(e.to_string())).await;
                                return Ok(Box::pin(tokio_stream::empty()));
                            }
                        })
                        .tools(self.tools.list())
                } else {
                    request
                        .clone()
                        .set_system_message(match self.system_prompt.clone().render() {
                            Ok(msg) => msg,
                            Err(e) => {
                                // Send error through the channel before returning empty stream
                                let _ = self.tx.send(ChatResponse::Fail(e.to_string())).await;
                                return Ok(Box::pin(tokio_stream::empty()));
                            }
                        })
                };

                match self.provider.chat(request).await {
                    Ok(response_stream) => {
                        let tx = self.tx.clone();
                        let actions = response_stream.then(move |response| {
                            let tx = tx.clone();
                            async move {
                                match response {
                                    Ok(resp) => Ok(Action::AssistantResponse(resp)),
                                    Err(e) => {
                                        if let forge_provider::Error::Provider { provider: _, error } = &e {
                                            if let forge_provider::ProviderError::UpstreamError(value) = error {
                                                let _ = tx.send(ChatResponse::Fail(serde_json::to_string(value).unwrap_or_else(|_| value.to_string()))).await;
                                            }
                                        }
                                        Err(Error::from(e))
                                    }
                                }
                            }
                        });
                        Ok(Box::pin(actions))
                    }
                    Err(e) => {
                        if let forge_provider::Error::Provider { provider: _, error } = &e {
                            if let forge_provider::ProviderError::UpstreamError(value) = error {
                                let _ = self.tx.send(ChatResponse::Fail(serde_json::to_string(value).unwrap_or_else(|_| value.to_string()))).await;
                            }
                        }
                        Err(e.into())
                    }
                }
            }
            Command::UserMessage(message) => {
                if let Err(e) = self.tx.send(message.clone()).await {
                    // Send error through the channel before returning empty stream
                    let _ = self.tx.send(ChatResponse::Fail(format!("Failed to send message: {}", e))).await;
                    return Ok(Box::pin(tokio_stream::empty()));
                }

                let stream: BoxStream<Action, Error> = Box::pin(tokio_stream::empty());
                Ok(stream)
            }
            Command::ToolCall(tool_call) => {
                match self.tools.call(&tool_call.name, tool_call.arguments.clone()).await {
                    Ok(content) => {
                        let tool_call_response = Action::ToolResponse(ToolResult {
                            content,
                            use_id: tool_call.call_id.clone(),
                            name: tool_call.name.clone(),
                            is_error: false,
                        });
                        Ok(Box::pin(tokio_stream::once(Ok(tool_call_response))))
                    }
                    Err(e) => {
                        // Send error through the channel before returning empty stream
                        let _ = self.tx.send(ChatResponse::Fail(format!("Tool call failed: {}", e))).await;
                        Ok(Box::pin(tokio_stream::empty()))
                    }
                }
            }
        }
    }
}
