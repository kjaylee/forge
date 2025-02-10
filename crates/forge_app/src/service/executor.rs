use std::sync::Arc;

use forge_domain::{
    AgentMessage, ChatRequest, ChatResponse, EnvironmentService, FileReadService, ProviderService,
    SystemContext, ToolService, Variables, Workflow,
};
use forge_stream::MpscStream;
use forge_walker::Walker;

use crate::workflow::ForgeWorkflow;
use crate::ForgeApp;

pub struct Executor<F> {
    app: Arc<F>,
}

impl<F: ForgeApp> Executor<F> {
    pub fn new(app: Arc<F>) -> Self {
        Self { app }
    }

    pub async fn execute(
        &self,
        chat_request: ChatRequest,
    ) -> anyhow::Result<MpscStream<anyhow::Result<AgentMessage<ChatResponse>>>> {
        let env = self.app.environment_service().get_environment().await?;
        let workflow = ForgeWorkflow::new(env.clone());
        let workflow: Workflow = workflow.into();
        let input = Variables::new_pair("task", chat_request.content);
        let custom_instructions = match chat_request.custom_instructions {
            Some(path) => Some(self.app.file_read_service().read(path).await?),
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
                    .parameters(&chat_request.model)
                    .await?
                    .tool_supported,
            ),
            custom_instructions,
            files,
        };

        Ok(workflow.execute(self.app.clone(), input, ctx))
    }
}
