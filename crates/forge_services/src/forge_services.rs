use std::path::{Path, PathBuf};
use std::sync::Arc;

use anyhow::Error;
use forge_app::{
    AttachmentService, ConversationService, EnvironmentService, FileDiscoveryService,
    FsCreateOutput, FsCreateService, FsPatchService, FsRemoveOutput, FsUndoOutput, HttpResponse,
    McpConfigManager, PatchOutput, ProviderService, ReadOutput, SearchResult, ShellOutput,
    TemplateService, WorkflowService,
};
use forge_domain::{
    Attachment, ChatCompletionMessage, Context, Conversation, ConversationId, Environment, File,
    McpConfig, Model, ModelId, PatchOperation, ResultStream, Scope, ToolCallFull, ToolDefinition,
    ToolOutput, Workflow,
};
use serde::Serialize;

use crate::attachment::ForgeChatRequest;
use crate::conversation::ForgeConversationService;
use crate::discovery::ForgeDiscoveryService;
use crate::mcp::{ForgeMcpManager, ForgeMcpService};
use crate::provider::ForgeProviderService;
use crate::template::ForgeTemplateService;
use crate::tool_services::{
    ForgeFetch, ForgeFollowup, ForgeFsCreate, ForgeFsPatch, ForgeFsRead, ForgeFsRemove,
    ForgeFsSearch, ForgeFsUndo, ForgeShell,
};
use crate::workflow::ForgeWorkflowService;
use crate::{
    CommandExecutorService, FileRemoveService, FsCreateDirsService, FsMetaService, FsReadService,
    FsSnapshotService, FsWriteService, InquireService, McpServer,
};

type McpService<F> = ForgeMcpService<ForgeMcpManager<F>, F, <F as McpServer>::Client>;

/// ForgeApp is the main application container that implements the App trait.
/// It provides access to all core services required by the application.
///
/// Type Parameters:
/// - F: The infrastructure implementation that provides core services like
///   environment, file reading, vector indexing, and embedding.
#[derive(Clone)]
pub struct ForgeServices<F: McpServer> {
    infra: Arc<F>,
    provider_service: Arc<ForgeProviderService>,
    conversation_service: Arc<ForgeConversationService<McpService<F>>>,
    template_service: Arc<ForgeTemplateService<F>>,
    attachment_service: Arc<ForgeChatRequest<F>>,
    workflow_service: Arc<ForgeWorkflowService<F>>,
    discovery_service: Arc<ForgeDiscoveryService<F>>,
    mcp_manager: Arc<ForgeMcpManager<F>>,
    file_create_service: Arc<ForgeFsCreate<F>>,
    file_read_service: Arc<ForgeFsRead<F>>,
    file_search_service: Arc<ForgeFsSearch>,
    file_remove_service: Arc<ForgeFsRemove<F>>,
    file_patch_service: Arc<ForgeFsPatch<F>>,
    file_undo_service: Arc<ForgeFsUndo<F>>,
    shell_service: Arc<ForgeShell<F>>,
    fetch_service: Arc<ForgeFetch>,
    followup_service: Arc<ForgeFollowup<F>>,
    mcp_service: Arc<McpService<F>>,
}

impl<F: McpServer + EnvironmentService + FsWriteService + FsMetaService + FsReadService>
    ForgeServices<F>
{
    pub fn new(infra: Arc<F>) -> Self {
        let mcp_manager = Arc::new(ForgeMcpManager::new(infra.clone()));
        let mcp_service = Arc::new(ForgeMcpService::new(mcp_manager.clone(), infra.clone()));
        let template_service = Arc::new(ForgeTemplateService::new(infra.clone()));
        let provider_service = Arc::new(ForgeProviderService::new(infra.clone()));
        let attachment_service = Arc::new(ForgeChatRequest::new(infra.clone()));

        let conversation_service = Arc::new(ForgeConversationService::new(mcp_service.clone()));

        let workflow_service = Arc::new(ForgeWorkflowService::new(infra.clone()));
        let suggestion_service = Arc::new(ForgeDiscoveryService::new(infra.clone()));
        let file_create_service = Arc::new(ForgeFsCreate::new(infra.clone()));
        let file_read_service = Arc::new(ForgeFsRead::new(infra.clone()));
        let file_search_service = Arc::new(ForgeFsSearch::new());
        let file_remove_service = Arc::new(ForgeFsRemove::new(infra.clone()));
        let file_patch_service = Arc::new(ForgeFsPatch::new(infra.clone()));
        let file_undo_service = Arc::new(ForgeFsUndo::new(infra.clone()));
        let shell_service = Arc::new(ForgeShell::new(infra.clone()));
        let fetch_service = Arc::new(ForgeFetch::new());
        let followup_service = Arc::new(ForgeFollowup::new(infra.clone()));
        Self {
            infra,
            conversation_service,
            attachment_service,
            provider_service,
            template_service,
            workflow_service,
            discovery_service: suggestion_service,
            mcp_manager,
            file_create_service,
            file_read_service,
            file_search_service,
            file_remove_service,
            file_patch_service,
            file_undo_service,
            shell_service,
            fetch_service,
            followup_service,
            mcp_service,
        }
    }
}

#[async_trait::async_trait]
impl<F: McpServer> ProviderService for ForgeServices<F> {
    async fn chat(
        &self,
        id: &ModelId,
        context: Context,
    ) -> ResultStream<ChatCompletionMessage, Error> {
        self.provider_service.chat(id, context).await
    }

    async fn models(&self) -> anyhow::Result<Vec<Model>> {
        self.provider_service.models().await
    }
}

#[async_trait::async_trait]
impl<I: McpServer + FsReadService + FsWriteService + EnvironmentService + FsMetaService>
    ConversationService for ForgeServices<I>
{
    async fn find(&self, id: &ConversationId) -> anyhow::Result<Option<Conversation>> {
        self.conversation_service.find(id).await
    }

    async fn upsert(&self, conversation: Conversation) -> anyhow::Result<()> {
        self.conversation_service.upsert(conversation).await
    }

    async fn create(&self, workflow: Workflow) -> anyhow::Result<Conversation> {
        self.conversation_service.create(workflow).await
    }

    async fn update<F, T>(&self, id: &ConversationId, f: F) -> anyhow::Result<T>
    where
        F: FnOnce(&mut Conversation) -> T + Send,
    {
        self.conversation_service.update(id, f).await
    }
}

#[async_trait::async_trait]
impl<F: McpServer + FsReadService + EnvironmentService> TemplateService for ForgeServices<F> {
    async fn register_template(&self, path: PathBuf) -> anyhow::Result<()> {
        self.template_service.register_template(path).await
    }

    async fn render(
        &self,
        template: impl ToString + Send,
        object: &(impl Serialize + Sync),
    ) -> anyhow::Result<String> {
        self.template_service.render(template, object).await
    }
}

#[async_trait::async_trait]
impl<F: McpServer + FsReadService + FsWriteService + EnvironmentService> AttachmentService
    for ForgeServices<F>
{
    async fn attachments(&self, url: &str) -> anyhow::Result<Vec<Attachment>> {
        self.attachment_service.attachments(url).await
    }
}

#[async_trait::async_trait]
impl<F: McpServer + FsWriteService + EnvironmentService> EnvironmentService for ForgeServices<F> {
    fn get_environment(&self) -> Environment {
        self.infra.get_environment()
    }
}

#[async_trait::async_trait]
impl<I: McpServer + FsReadService + FsWriteService> WorkflowService for ForgeServices<I> {
    async fn resolve(&self, path: Option<PathBuf>) -> PathBuf {
        self.workflow_service.resolve(path).await
    }

    async fn read(&self, path: Option<&Path>) -> anyhow::Result<Workflow> {
        self.workflow_service.read(path).await
    }

    async fn write(&self, path: Option<&Path>, workflow: &Workflow) -> anyhow::Result<()> {
        self.workflow_service.write(path, workflow).await
    }

    async fn update_workflow<F>(&self, path: Option<&Path>, f: F) -> anyhow::Result<Workflow>
    where
        F: FnOnce(&mut Workflow) + Send,
    {
        self.workflow_service.update_workflow(path, f).await
    }
}

#[async_trait::async_trait]
impl<F: McpServer + FsReadService + FsWriteService + EnvironmentService> FileDiscoveryService
    for ForgeServices<F>
{
    async fn collect(&self, max_depth: Option<usize>) -> anyhow::Result<Vec<File>> {
        self.discovery_service.collect(max_depth).await
    }
}

#[async_trait::async_trait]
impl<F: McpServer + FsReadService + FsWriteService + FsMetaService + EnvironmentService>
    McpConfigManager for ForgeServices<F>
{
    async fn read(&self) -> anyhow::Result<McpConfig> {
        self.mcp_manager.read().await
    }

    async fn write(&self, config: &McpConfig, scope: &Scope) -> anyhow::Result<()> {
        self.mcp_manager.write(config, scope).await
    }
}

#[async_trait::async_trait]
impl<F: McpServer + FsWriteService + FsMetaService + FsReadService + FsCreateDirsService>
    FsCreateService for ForgeServices<F>
{
    async fn create(
        &self,
        path: String,
        content: String,
        overwrite: bool,
        capture_snapshot: bool,
    ) -> anyhow::Result<FsCreateOutput> {
        self.file_create_service
            .create(path, content, overwrite, capture_snapshot)
            .await
    }
}

#[async_trait::async_trait]
impl<F: McpServer + FsWriteService> FsPatchService for ForgeServices<F> {
    async fn patch(
        &self,
        path: String,
        search: Option<String>,
        operation: PatchOperation,
        content: String,
    ) -> anyhow::Result<PatchOutput> {
        self.file_patch_service
            .patch(path, search, operation, content)
            .await
    }
}

#[async_trait::async_trait]
impl<F: McpServer + FsReadService + EnvironmentService + FsMetaService> forge_app::FsReadService
    for ForgeServices<F>
{
    async fn read(
        &self,
        path: String,
        start_line: Option<u64>,
        end_line: Option<u64>,
    ) -> anyhow::Result<ReadOutput> {
        self.file_read_service
            .read(path, start_line, end_line)
            .await
    }
}

#[async_trait::async_trait]
impl<F: McpServer + FileRemoveService> forge_app::FsRemoveService for ForgeServices<F> {
    async fn remove(&self, path: String) -> anyhow::Result<FsRemoveOutput> {
        self.file_remove_service.remove(path).await
    }
}

#[async_trait::async_trait]
impl<F: McpServer + FsReadService> forge_app::FsSearchService for ForgeServices<F> {
    async fn search(
        &self,
        path: String,
        regex: Option<String>,
        file_pattern: Option<String>,
    ) -> anyhow::Result<Option<SearchResult>> {
        self.file_search_service
            .search(path, regex, file_pattern)
            .await
    }
}

#[async_trait::async_trait]
impl<F: McpServer + InquireService> forge_app::FollowUpService for ForgeServices<F> {
    async fn follow_up(
        &self,
        question: String,
        options: Vec<String>,
        multiple: Option<bool>,
    ) -> anyhow::Result<Option<String>> {
        self.followup_service
            .follow_up(question, options, multiple)
            .await
    }
}

#[async_trait::async_trait]
impl<F: McpServer + FsMetaService + FsReadService + FsSnapshotService> forge_app::FsUndoService
    for ForgeServices<F>
{
    async fn undo(&self, path: String) -> anyhow::Result<FsUndoOutput> {
        self.file_undo_service.undo(path).await
    }
}

#[async_trait::async_trait]
impl<F: McpServer> forge_app::NetFetchService for ForgeServices<F> {
    async fn fetch(&self, url: String, raw: Option<bool>) -> anyhow::Result<HttpResponse> {
        self.fetch_service.fetch(url, raw).await
    }
}

#[async_trait::async_trait]
impl<F: McpServer + CommandExecutorService + EnvironmentService> forge_app::ShellService
    for ForgeServices<F>
{
    async fn execute(
        &self,
        command: String,
        cwd: PathBuf,
        keep_ansi: bool,
    ) -> anyhow::Result<ShellOutput> {
        self.shell_service.execute(command, cwd, keep_ansi).await
    }
}

#[async_trait::async_trait]
impl<F: McpServer + FsReadService + FsMetaService + EnvironmentService + FsWriteService>
    forge_app::McpService for ForgeServices<F>
{
    async fn list(&self) -> anyhow::Result<Vec<ToolDefinition>> {
        self.mcp_service.list().await
    }

    async fn call(&self, call: ToolCallFull) -> anyhow::Result<ToolOutput> {
        self.mcp_service.call(call).await
    }
}
