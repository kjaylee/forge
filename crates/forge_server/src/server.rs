use std::sync::Arc;

use forge_env::Environment;
use forge_provider::{Model, ModelId, Provider, Request, Response};
use forge_tool::{ToolDefinition, ToolEngine};
use tokio::sync::{mpsc, Mutex};
use tokio_stream::wrappers::ReceiverStream;
use tokio_stream::Stream;

use crate::app::{Action, App, ChatRequest, ChatResponse};
use crate::completion::{Completion, File};
use crate::executor::ChatCommandExecutor;
use crate::runtime::{ApplicationRuntime, AppState};
use crate::{Result, Storage};

#[derive(Clone)]
pub struct Server<S: Storage> {
    provider: Arc<Provider<Request, Response, forge_provider::Error>>,
    tools: Arc<ToolEngine>,
    completions: Arc<Completion>,
    runtime: Arc<ApplicationRuntime>,
    env: Environment,
    api_key: String,
    storage: Arc<S>,
    inital_request: Request,
}

impl<S: Storage + 'static> Server<S> {
    pub fn new(env: Environment, storage: Arc<S>, api_key: impl Into<String>) -> Self {
        let tools = ToolEngine::new();
        let inital_request = Request::new(ModelId::default());

        let cwd: String = env.cwd.clone();
        let api_key: String = api_key.into();
        Self {
            env,
            provider: Arc::new(Provider::open_router(api_key.clone(), None)),
            tools: Arc::new(tools),
            completions: Arc::new(Completion::new(cwd.clone())),
            runtime: Arc::new(ApplicationRuntime),
            api_key,
            storage,
            inital_request,
        }
    }

    pub async fn completions(&self) -> Result<Vec<File>> {
        self.completions.list().await
    }

    pub fn tools(&self) -> Vec<ToolDefinition> {
        self.tools.list()
    }

    pub async fn models(&self) -> Result<Vec<Model>> {
        Ok(self.provider.models().await?)
    }

    pub fn storage(&self) -> Arc<S> {
        self.storage.clone()
    }

    pub async fn chat(
        &self,
        mut chat: ChatRequest,
    ) -> Result<impl Stream<Item = ChatResponse> + Send> {
        // if the conversation id is not provided, then generate a new one.
        let conversation_id = chat
            .conversation_id
            .take()
            .unwrap_or_else(|| uuid::Uuid::new_v4().to_string());

        let content = chat.content.clone();
        let request = chat
            .conversation_id(Some(conversation_id.clone()))
            .content(format!("<task>{}</task>", content));

        dbg!(&conversation_id);

        let exec_ctx = {
            // 1. pull the conversation context from database.
            let mut exec_ctx = self
                .storage
                .get(&conversation_id)
                .await?
                .unwrap_or_else(|| AppState {
                    app: App::new(self.inital_request.clone(), conversation_id.clone()),
                    action: Action::UserMessage(request.clone()),
                });
            // since we are not trying to restore, in order to execute the present request
            // we replace the action with the new request.
            exec_ctx.action = Action::UserMessage(request);
            Arc::new(Mutex::new(exec_ctx))
        };

        let (tx, rx) = mpsc::channel::<ChatResponse>(100);
        // send the conversation id to the client.
        let _ = tx
            .send(ChatResponse::ConversationId(conversation_id.clone()))
            .await;

        let executor = ChatCommandExecutor::new(
            self.env.clone(),
            self.api_key.clone(),
            tx,
            self.storage.clone(),
        );
        let runtime = self.runtime.clone();
        let storage = self.storage.clone();

        tokio::spawn(async move {
            let guard = exec_ctx.lock().await;
            let app = Arc::new(Mutex::new(guard.app.clone()));
            let action = guard.action.clone();
            drop(guard);

            let result = runtime
                .execute(app.clone(), action, Arc::new(executor))
                .await;

            if let Ok(action) = result.as_ref() {
                // if everything is executed successfully, then save the state.
                let guard = app.lock().await;
                let _ = storage
                    .save(
                        &conversation_id,
                        &AppState { app: guard.clone(), action: action.clone() },
                    )
                    .await;
            }

            result
        });

        Ok(ReceiverStream::new(rx))
    }
}
