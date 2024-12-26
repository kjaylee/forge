use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use forge_prompt::Prompt;
use forge_provider::{Message, Model, ModelId, Provider, Request, Response, ToolResult, ToolUse};
use forge_tool::{Tool, ToolEngine, ToolName};
use serde_json::Value;
use tokio::sync::mpsc;
use tokio_stream::wrappers::ReceiverStream;
use tokio_stream::{Stream, StreamExt};
use tracing::info;

use crate::completion::{Completion, File};
use crate::template::PromptTemplate;
use crate::{Error, Result};

#[derive(Debug, serde::Serialize)]
pub enum ChatEvent {
    Text(String),
    ToolUseStart(ToolName),
    ToolUseEnd(String, Value),
    Complete,
    Fail(String),
}

#[allow(unused)]
#[derive(Debug, serde::Deserialize)]
pub struct ChatRequest {
    // Add fields as needed, for example:
    pub message: String,
    pub model: ModelId,
}

#[derive(Debug, Clone)]
struct Context<A> {
    request: Arc<Mutex<A>>,
}

impl<A: Clone> Context<A> {
    fn new(request: A) -> Self {
        Self { request: Arc::new(Mutex::new(request)) }
    }

    fn get(&self) -> A {
        self.request.lock().unwrap().clone()
    }

    fn set(&self, update: impl FnOnce(A) -> A) -> A {
        let mut request = self.request.lock().unwrap();
        *request = update(request.clone());
        request.clone()
    }
}

#[derive(Clone)]
pub struct Server {
    provider: Arc<Provider<Request, Response, forge_provider::Error>>,
    tools: Arc<ToolEngine>,
    context: Context<Request>,
    completions: Arc<Completion>,
    models_cache: Arc<Mutex<Option<(Vec<Model>, Instant)>>>,
}

const MODELS_CACHE_DURATION: Duration = Duration::from_secs(10000); // Cache for 1 hour

impl Server {
    pub async fn completions(&self) -> Result<Vec<File>> {
        self.completions.list().await
    }

    pub fn new(cwd: impl Into<String>, api_key: impl Into<String>) -> Server {
        let tools = ToolEngine::default();
        let request = Request::new(ModelId::default())
            .add_message(Message::system(include_str!("./prompts/system.md")))
            .tools(tools.list());

        Self {
            provider: Arc::new(Provider::open_router(api_key.into(), None)),
            tools: Arc::new(tools),
            context: Context::new(request),
            completions: Arc::new(Completion::new(cwd)),
            models_cache: Arc::new(Mutex::new(None)),
        }
    }

    pub fn tools(&self) -> Vec<Tool> {
        self.tools.list()
    }

    pub fn context(&self) -> Request {
        self.context.get()
    }

    pub async fn models(&self) -> Result<Vec<Model>> {
        // Check cache first
        if let Some((cached_models, cache_time)) = self.models_cache.lock().unwrap().as_ref() {
            if cache_time.elapsed() < MODELS_CACHE_DURATION {
                return Ok(cached_models.clone());
            }
        }

        // Cache miss or expired, fetch new models
        let models = self.provider.models().await?;
        
        // Update cache
        *self.models_cache.lock().unwrap() = Some((models.clone(), Instant::now()));
        
        Ok(models)
    }

    pub async fn chat(&self, chat: ChatRequest) -> Result<impl Stream<Item = ChatEvent> + Send> {
        dbg!(&chat);
        let (tx, rx) = mpsc::channel::<ChatEvent>(100);

        let prompt = Prompt::parse(chat.message.clone()).unwrap_or(Prompt::new(chat.message));
        let mut message = PromptTemplate::task(prompt.to_string());

        for file in prompt.files() {
            let content = tokio::fs::read_to_string(file.clone()).await?;
            message = message.append(PromptTemplate::file(file, content));
        }

        self.context
            .set(|request| request.add_message(message).model(chat.model));

        let this = self.clone();
        tokio::task::spawn(async move {
            match this.run_forever(&tx).await {
                Ok(_) => {}
                Err(e) => tx.send(ChatEvent::Fail(e.to_string())).await.unwrap(),
            }
        });

        Ok(ReceiverStream::new(rx))
    }

    async fn run_forever(&self, tx: &mpsc::Sender<ChatEvent>) -> Result<()> {
        loop {
            let mut pending_request = false;
            let mut empty_response = true;

            let mut response = self.provider.chat(self.context.get()).await?;

            while let Some(message) = response.next().await {
                empty_response = false;
                let message = message?;
                if message.tool_use.is_empty() {
                    tx.send(ChatEvent::Text(message.message.content))
                        .await
                        .unwrap();
                } else {
                    for tool in message.tool_use.into_iter() {
                        let tool_result = self.use_tool(tool.clone(), tx).await?;
                        self.context
                            .set(|request| request.add_tool_result(tool_result));

                        pending_request = true
                    }
                }
            }

            if empty_response {
                return Err(Error::EmptyResponse);
            }

            if !pending_request {
                return Ok(());
            }
        }
    }

    async fn use_tool(&self, tool: ToolUse, tx: &mpsc::Sender<ChatEvent>) -> Result<ToolResult> {
        let content = if let Some(tool_name) = tool.tool_name {
            info!(tool.input);
            tx.send(ChatEvent::ToolUseStart(tool_name.clone())).await?;
            let content = self
                .tools
                .call(&tool_name, serde_json::from_str(&tool.input).unwrap())
                .await?;

            tx.send(ChatEvent::ToolUseEnd(
                tool_name.into_string(),
                content.clone(),
            ))
            .await?;
            
            content
        } else {
            Value::default()
        };

        Ok(ToolResult {
            tool_use_id: tool.tool_use_id,
            content,
        })
    }
}
