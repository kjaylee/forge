use std::sync::{Arc, RwLock};

use forge_env::Environment;
use forge_provider::{Model, ModelId, Provider, Request, Response};
use forge_tool::{ToolDefinition, ToolEngine};
use tokio::sync::mpsc;
use tokio_stream::wrappers::ReceiverStream;
use tokio_stream::Stream;

use crate::app::{Action, App, ChatRequest, ChatResponse};
use crate::completion::{Completion, File};
use crate::executor::ChatCommandExecutor;
use crate::runtime::ApplicationRuntime;
use crate::{Result, Storage};

#[derive(Clone)]
pub struct Server<S: Storage> {
    provider: Arc<Provider<Request, Response, forge_provider::Error>>,
    tools: Arc<ToolEngine>,
    completions: Arc<Completion>,
    runtime: Arc<ApplicationRuntime<App, S>>,
    env: Environment,
    api_key: String,
    storage: Arc<S>,
    base_context: Request,
}

impl<S: Storage + 'static> Server<S> {
    pub fn new(env: Environment, storage: Arc<S>, api_key: impl Into<String>) -> Self {
        let tools = ToolEngine::new();
        let request = Request::new(ModelId::default());

        let cwd: String = env.cwd.clone();
        let api_key: String = api_key.into();
        Self {
            env,
            provider: Arc::new(Provider::open_router(api_key.clone(), None)),
            tools: Arc::new(tools),
            completions: Arc::new(Completion::new(cwd.clone())),
            runtime: Arc::new(ApplicationRuntime::new(App::default(), storage.clone())),
            api_key,
            storage,
            base_context: request,
        }
    }

    pub async fn completions(&self) -> Result<Vec<File>> {
        self.completions.list().await
    }

    pub fn tools(&self) -> Vec<ToolDefinition> {
        self.tools.list()
    }

    pub fn system_prompt(&self) -> Request {
        self.base_context.clone()
    }

    pub async fn models(&self) -> Result<Vec<Model>> {
        Ok(self.provider.models().await?)
    }

    pub fn storage(&self) -> Arc<S> {
        self.storage.clone()
    }

    pub async fn chat(
        &self,
        chat: ChatRequest,
        context: Arc<RwLock<Request>>,
    ) -> Result<impl Stream<Item = ChatResponse> + Send> {
        let conversation_id = chat
            .conversation_id
            .clone()
            .expect("`conversation_id` is expected to be present!");
        let (tx, rx) = mpsc::channel::<ChatResponse>(100);
        // send the conversation id to the client.
        tx.send(ChatResponse::ConversationId(conversation_id.clone()))
            .await?;

        let executor = ChatCommandExecutor::new(self.env.clone(), self.api_key.clone(), tx);
        let runtime = self.runtime.clone();
        let storage = self.storage.clone();
        let message = format!("<task>{}</task>", chat.content);

        tokio::spawn(async move {
            let result = runtime
                .clone()
                .execute(
                    context.clone(),
                    Action::UserMessage(chat.content(message)),
                    Arc::new(executor),
                )
                .await;

            // once everything is executed, update the context in db.
            let data = context.read().unwrap().clone();
            // TODO: handle save error gracefully.
            let _ = storage.save(&conversation_id, &data).await;
            result
        });

        Ok(ReceiverStream::new(rx))
    }
}
