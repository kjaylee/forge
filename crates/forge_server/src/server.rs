use std::sync::Arc;

use forge_env::Environment;
use forge_provider::{Model, ModelId, Provider, Request, Response};
use forge_tool::{ToolDefinition, ToolEngine};
use tokio::sync::{mpsc, Mutex};
use tokio_stream::wrappers::ReceiverStream;
use tokio_stream::Stream;

use crate::app::{Action, App, ChatResponse};
use crate::completion::{Completion, File};
use crate::executor::ChatCommandExecutor;
use crate::runtime::{ApplicationRuntime, ExecutionContext};
use crate::{Result, Storage};

#[derive(Clone)]
pub struct Server<S: Storage> {
    provider: Arc<Provider<Request, Response, forge_provider::Error>>,
    tools: Arc<ToolEngine>,
    completions: Arc<Completion>,
    runtime: Arc<ApplicationRuntime<S>>,
    env: Environment,
    api_key: String,
    storage: Arc<S>,
    base_app: App,
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
            runtime: Arc::new(ApplicationRuntime::new(storage.clone())),
            api_key,
            storage,
            base_app: App::new(request),
        }
    }

    pub async fn completions(&self) -> Result<Vec<File>> {
        self.completions.list().await
    }

    pub fn tools(&self) -> Vec<ToolDefinition> {
        self.tools.list()
    }

    pub fn app(&self) -> App {
        self.base_app.clone()
    }

    pub async fn models(&self) -> Result<Vec<Model>> {
        Ok(self.provider.models().await?)
    }

    pub fn storage(&self) -> Arc<S> {
        self.storage.clone()
    }

    pub async fn chat(
        &self,
        store_point: Arc<Mutex<ExecutionContext<App, Action>>>,
    ) -> Result<impl Stream<Item = ChatResponse> + Send> {
        let conversation_id = {
            store_point
                .lock()
                .await
                .app
                .conversation_id()
                .clone()
                .expect("`conversation_id` is expected to be present!")
                .to_string()
        };
        let (tx, rx) = mpsc::channel::<ChatResponse>(100);
        // send the conversation id to the client.
        tx.send(ChatResponse::ConversationId(conversation_id.clone()))
            .await?;
        let executor = ChatCommandExecutor::new(self.env.clone(), self.api_key.clone(), tx);
        let runtime = self.runtime.clone();
        let storage = self.storage.clone();

        tokio::spawn(async move {
            let guard = store_point.lock().await;
            let app = Arc::new(Mutex::new(guard.app.clone()));
            let action = guard.action.clone();
            drop(guard);

            let result = runtime
                .execute(app.clone(), action, Arc::new(executor))
                .await;

            if result.is_ok() {
                // if everything is executed successfully, then save the state.
                let guard = app.lock().await;
                let _ = storage
                    .save(
                        &conversation_id,
                        &ExecutionContext {
                            app: guard.clone(),
                            action: Action::AssistantResponse(Response {
                                content: "".to_string(),
                                tool_call: vec![],
                                finish_reason: None,
                            }),
                        },
                    )
                    .await;
            }

            result
        });

        Ok(ReceiverStream::new(rx))
    }
}
