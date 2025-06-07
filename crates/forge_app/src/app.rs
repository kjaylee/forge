use std::sync::Arc;

use anyhow::Result;
use forge_domain::*;
use forge_stream::MpscStream;

use crate::{
    AttachmentService, ConversationService, EnvironmentService, FileDiscoveryService, Orchestrator,
    ProviderService, Services, ToolService, WorkflowService,
};

/// ForgeApp handles the core chat functionality by orchestrating various
/// services. It encapsulates the complex logic previously contained in the
/// ForgeAPI chat method.
pub struct ForgeApp<S: Services> {
    services: Arc<S>,
}

impl<S: Services> ForgeApp<S> {
    /// Creates a new ForgeApp instance with the provided services.
    pub fn new(services: Arc<S>) -> Self {
        Self { services }
    }

    /// Executes a chat request and returns a stream of responses.
    /// This method contains the core chat logic extracted from ForgeAPI.
    pub async fn chat(
        &self,
        mut chat: ChatRequest,
    ) -> Result<MpscStream<Result<ChatResponse, anyhow::Error>>> {
        let services = self.services.clone();

        // Get the conversation for the chat request
        let conversation = services
            .conversation_service()
            .find(&chat.conversation_id)
            .await
            .unwrap_or_default()
            .expect("conversation for the request should've been created at this point.");

        // Get tool definitions and models
        let tool_definitions = services.tool_service().list().await?;
        let models = services.provider_service().models().await?;

        // Discover files using the discovery service
        let workflow = services
            .workflow_service()
            .read(None)
            .await
            .unwrap_or_default();
        let max_depth = workflow.max_walker_depth;
        let files = services
            .file_discovery_service()
            .collect(max_depth)
            .await?
            .into_iter()
            .map(|f| f.path)
            .collect::<Vec<_>>();

        // Get environment for orchestrator creation
        let environment = services.environment_service().get_environment();

        // Always try to get attachments and overwrite them
        let attachments = services
            .attachment_service()
            .attachments(&chat.event.value.to_string())
            .await?;
        chat.event = chat.event.attachments(attachments);

        // Create the orchestrator with all necessary dependencies
        let orch = Orchestrator::new(services.clone(), environment.clone(), conversation)
            .tool_definitions(tool_definitions)
            .models(models)
            .files(files);

        // Create and return the stream
        let stream = MpscStream::spawn(
            |tx: tokio::sync::mpsc::Sender<Result<ChatResponse, anyhow::Error>>| {
                async move {
                    let tx = Arc::new(tx);

                    // Execute dispatch and always save conversation afterwards
                    let mut orch = orch.sender(tx.clone());
                    let dispatch_result = orch.chat(chat.event).await;

                    // Always save conversation using get_conversation()
                    let conversation = orch.get_conversation().clone();
                    let save_result = services.conversation_service().upsert(conversation).await;

                    // Send any error to the stream (prioritize dispatch error over save error)
                    #[allow(clippy::collapsible_if)]
                    if let Some(err) = dispatch_result.err().or(save_result.err()) {
                        if let Err(e) = tx.send(Err(err)).await {
                            tracing::error!("Failed to send error to stream: {}", e);
                        }
                    }
                }
            },
        );

        Ok(stream)
    }

    /// Compacts the context of the main agent for the given conversation and
    /// persists it. Returns metrics about the compaction (original vs.
    /// compacted tokens and messages).
    pub async fn compact_conversation(
        &self,
        _conversation_id: &ConversationId,
    ) -> Result<CompactionResult> {
        // TODO: Implement actual compaction logic
        // For now, return a dummy result indicating no compaction was performed
        Ok(CompactionResult::new(0, 0, 0, 0))
    }
}
