use std::sync::Arc;

use forge_app::{EnvironmentService, FileReadService, Infrastructure};
use forge_domain::{
    AgentMessage, App, ChatRequest, ChatResponse, ConcurrentWorkflow, SystemContext, ToolService,
    Workflow,
};
use forge_stream::MpscStream;
use forge_walker::Walker;

pub struct ForgeExecutorService<F> {
    app: Arc<F>,
    workflow: ConcurrentWorkflow,
}
impl<F: Infrastructure + App> ForgeExecutorService<F> {
    pub fn new(app: Arc<F>) -> Self {
        Self { app, workflow: ConcurrentWorkflow::default() }
    }
}

impl<F: Infrastructure + App> ForgeExecutorService<F> {
    pub async fn reset(&self, workflow: Option<Workflow>) {
        self.workflow.reset(workflow).await;
    }

    pub async fn chat(
        &self,
        chat_request: ChatRequest,
    ) -> anyhow::Result<MpscStream<anyhow::Result<AgentMessage<ChatResponse>>>> {
        let env = self.app.environment_service().get_environment();
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
            tool_supported: Some(true),
            custom_instructions,
            files,
        };

        Ok(self.workflow.execute(self.app.clone(), chat_request, ctx))
    }
}
