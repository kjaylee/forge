use std::sync::Arc;

use anyhow::Result;
use forge_domain::{ConversationId, ConversationService, File, Services};
use forge_services::Infrastructure;
use forge_walker::Walker;

pub struct ForgeSuggestionService<F> {
    domain: Arc<F>,
}

impl<F: Services> ForgeSuggestionService<F> {
    pub fn new(domain: Arc<F>) -> Self {
        Self { domain }
    }
}

impl<F: Services + Infrastructure> ForgeSuggestionService<F> {
    pub async fn suggestions(&self, conversation_id: Option<&ConversationId>) -> Result<Vec<File>> {
        // FIXME: conversation_id should not be optional
        // Alternatively we can use CWD instead of conversation_id
        // Try to get the CWD from an active conversation if conversation_id is provided
        let cwd = if let Some(id) = conversation_id {
            // Try to get the conversation using the ConversationService trait method
            let conversation_service = self.domain.conversation_service();
            if let Ok(Some(conversation)) =
                ConversationService::find(conversation_service, id).await
            {
                conversation.cwd().clone()
            } else {
                // Fall back to current directory if conversation not found
                std::env::current_dir()?
            }
        } else {
            // If no conversation_id provided, use current directory
            std::env::current_dir()?
        };

        let walker = Walker::max_all().cwd(cwd);

        let files = walker.get().await?;
        Ok(files
            .into_iter()
            .map(|file| File { path: file.path.clone(), is_dir: file.is_dir() })
            .collect())
    }
}
