use std::sync::Arc;

use forge_app::{EnvironmentService, FileReadService, ForgeWorkflow, Infrastructure};
use forge_domain::{
    AgentMessage, App, ChatRequest, ChatResponse, ProviderService, SystemContext, ToolService,
    Workflow,
};
use forge_stream::MpscStream;
use forge_walker::Walker;

use crate::ExecutorService;

pub struct ForgeExecutorService<F> {
    app: Arc<F>,
}
impl<F> ForgeExecutorService<F> {
    pub fn new(app: Arc<F>) -> Self {
        Self { app }
    }
}

#[async_trait::async_trait]
impl<F: Infrastructure + App> ExecutorService for ForgeExecutorService<F> {
    async fn chat(
        &self,
        chat_request: ChatRequest,
    ) -> anyhow::Result<MpscStream<anyhow::Result<AgentMessage<ChatResponse>>>> {
        let env = self.app.environment_service().get_environment();

        // TODO: Load the workflow from a YAML/TOML file
        let workflow = ForgeWorkflow::new(env.clone());
        let workflow: Workflow = workflow.into();
        let custom_instructions = match chat_request.custom_instructions {
            Some(ref path) => Some(self.app.file_read_service().read(path.clone()).await?),
            None => None,
        };

        let mut files = Walker::max_all()
            .max_depth(2)
            .cwd(env.cwd.clone())
            .get()
            .await?
            .iter()
            .map(|f| f.path.to_string())
            .collect::<Vec<_>>();

        // Sort the files alphabetically to ensure consistent ordering
        files.sort();

        let ctx = SystemContext {
            env: Some(env),
            tool_information: Some(self.app.tool_service().usage_prompt()),
            tool_supported: Some(
                self.app
                    .provider_service()
                    .parameters(&chat_request.model.clone())
                    .await?
                    .tool_supported,
            ),
            custom_instructions,
            files,
        };

        Ok(workflow.execute(self.app.clone(), chat_request, ctx))
    }
}
