use std::path::{Path, PathBuf};
use std::sync::Arc;

use anyhow::Result;
use forge_app::{
    AttachmentService, ConversationService, EnvironmentService, FileDiscoveryService,
    FollowUpService, ForgeApp, FsCreateService, FsPatchService, FsReadService, FsRemoveService,
    FsSearchService, FsUndoService, McpConfigManager, McpService, NetFetchService, ProviderService,
    ShellService, TemplateService, WorkflowService,
};
use forge_domain::*;
use forge_infra::ForgeInfra;
use forge_services::{CommandExecutor, ForgeServices};
use forge_stream::MpscStream;

use crate::API;

pub struct ForgeAPI<A, F> {
    app: Arc<A>,
    infra: Arc<F>,
}

impl<A, F> ForgeAPI<A, F> {
    pub fn new(app: Arc<A>, infra: Arc<F>) -> Self {
        Self { app, infra }
    }
}

impl ForgeAPI<ForgeServices<ForgeInfra>, ForgeInfra> {
    pub fn init(restricted: bool) -> Self {
        let infra = Arc::new(ForgeInfra::new(restricted));
        let app = Arc::new(ForgeServices::new(infra.clone()));
        ForgeAPI::new(app, infra)
    }
}

#[async_trait::async_trait]
impl<
        A: ProviderService
            + FsReadService
            + FsCreateService
            + FsSearchService
            + NetFetchService
            + FsRemoveService
            + FsPatchService
            + FsUndoService
            + ShellService
            + FollowUpService
            + EnvironmentService
            + WorkflowService
            + ConversationService
            + McpService
            + AttachmentService
            + FileDiscoveryService
            + TemplateService
            + McpConfigManager
            + Clone,
        F: CommandExecutor,
    > API for ForgeAPI<A, F>
{
    async fn discover(&self) -> Result<Vec<File>> {
        self.app.collect(None).await
    }

    async fn tools(&self) -> anyhow::Result<Vec<ToolDefinition>> {
        let forge_app = ForgeApp::new(self.app.clone());
        forge_app.list_tools().await
    }

    async fn models(&self) -> Result<Vec<Model>> {
        Ok(self.app.models().await?)
    }

    async fn chat(
        &self,
        chat: ChatRequest,
    ) -> anyhow::Result<MpscStream<Result<ChatResponse, anyhow::Error>>> {
        // Create a ForgeApp instance and delegate the chat logic to it
        let forge_app = ForgeApp::new(self.app.clone());
        forge_app.chat(chat).await
    }

    async fn init_conversation<W: Into<Workflow> + Send + Sync>(
        &self,
        workflow: W,
    ) -> anyhow::Result<Conversation> {
        ConversationService::create_conversation(self.app.as_ref(), workflow.into()).await
    }

    async fn upsert_conversation(&self, conversation: Conversation) -> anyhow::Result<()> {
        self.app.upsert(conversation).await
    }

    async fn compact_conversation(
        &self,
        conversation_id: &ConversationId,
    ) -> anyhow::Result<CompactionResult> {
        let forge_app = ForgeApp::new(self.app.clone());
        forge_app.compact_conversation(conversation_id).await
    }

    fn environment(&self) -> Environment {
        self.app.as_ref().get_environment().clone()
    }

    async fn read_workflow(&self, path: Option<&Path>) -> anyhow::Result<Workflow> {
        WorkflowService::read_workflow(self.app.as_ref(), path).await
    }

    async fn write_workflow(&self, path: Option<&Path>, workflow: &Workflow) -> anyhow::Result<()> {
        WorkflowService::write_workflow(self.app.as_ref(), path, workflow).await
    }

    async fn update_workflow<T>(&self, path: Option<&Path>, f: T) -> anyhow::Result<Workflow>
    where
        T: FnOnce(&mut Workflow) + Send,
    {
        self.app.update_workflow(path, f).await
    }

    async fn conversation(
        &self,
        conversation_id: &ConversationId,
    ) -> anyhow::Result<Option<Conversation>> {
        self.app.find(conversation_id).await
    }

    async fn execute_shell_command(
        &self,
        command: &str,
        working_dir: PathBuf,
    ) -> anyhow::Result<CommandOutput> {
        self.infra
            .execute_command(command.to_string(), working_dir)
            .await
    }
    async fn read_mcp_config(&self) -> Result<McpConfig> {
        McpConfigManager::read_mcp_config(self.app.as_ref())
            .await
            .map_err(|e| anyhow::anyhow!(e))
    }

    async fn write_mcp_config(&self, scope: &Scope, config: &McpConfig) -> Result<()> {
        McpConfigManager::write_mcp_config(self.app.as_ref(), config, scope)
            .await
            .map_err(|e| anyhow::anyhow!(e))
    }

    async fn execute_shell_command_raw(
        &self,
        command: &str,
    ) -> anyhow::Result<std::process::ExitStatus> {
        self.infra.execute_command_raw(command).await
    }
}
