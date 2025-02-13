use std::path::PathBuf;
use std::sync::Arc;

use anyhow::Result;
use forge_app::{EnvironmentService, ForgeApp, Infrastructure};
use forge_domain::*;
use forge_infra::ForgeInfra;
use forge_stream::MpscStream;

use crate::executor::ForgeExecutorService;
use crate::suggestion::ForgeSuggestionService;
use crate::workflow_loader::WorkflowLoader;
use crate::{ExecutorService, SuggestionService, API};

pub struct ForgeAPI<F> {
    app: Arc<F>,
    _executor_service: ForgeExecutorService<F>,
    _suggestion_service: ForgeSuggestionService<F>,
    workflow_loader: WorkflowLoader<F>,
}

impl<F: App + Infrastructure> ForgeAPI<F> {
    pub fn new(app: Arc<F>, workflow: Workflow) -> Self {
        Self {
            app: app.clone(),
            _executor_service: ForgeExecutorService::new(app.clone(), workflow),
            _suggestion_service: ForgeSuggestionService::new(app.clone()),
            workflow_loader: WorkflowLoader::new(app),
        }
    }
}

impl ForgeAPI<ForgeApp<ForgeInfra>> {
    pub async fn init(restricted: bool, workflow: PathBuf) -> Result<Self> {
        let infra = Arc::new(ForgeInfra::new(restricted));
        let app = Arc::new(ForgeApp::new(infra));
        let workflow = WorkflowLoader::new(app.clone()).load(workflow).await?;
        Ok(ForgeAPI::new(app, workflow))
    }
}

#[async_trait::async_trait]
impl<F: App + Infrastructure> API for ForgeAPI<F> {
    async fn suggestions(&self) -> Result<Vec<File>> {
        self._suggestion_service.suggestions().await
    }

    async fn tools(&self) -> Vec<ToolDefinition> {
        self.app.tool_service().list()
    }

    async fn models(&self) -> Result<Vec<Model>> {
        Ok(self.app.provider_service().models().await?)
    }

    async fn chat(
        &self,
        chat: ChatRequest,
    ) -> anyhow::Result<MpscStream<Result<AgentMessage<ChatResponse>, anyhow::Error>>> {
        Ok(self._executor_service.chat(chat).await?)
    }

    async fn reset(&self) -> anyhow::Result<()> {
        self._executor_service.reset().await
    }

    async fn set_workflow(&self, path: PathBuf) -> anyhow::Result<()> {
        self._executor_service
            .set_workflow(self.workflow_loader.load(path).await?)
            .await?;
        Ok(())
    }

    fn environment(&self) -> Environment {
        self.app.environment_service().get_environment().clone()
    }
}
