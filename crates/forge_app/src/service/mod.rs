mod api;
mod chat;
mod env;
mod file_read;
mod provider;
mod suggestion;
mod system_prompt;
#[cfg(test)]
mod test;
mod tool_service;
mod ui;
mod user_prompt;
mod workflow_title;

pub use api::APIService;
pub use chat::ChatService;
pub use suggestion::SuggestionService;
pub use ui::UIService;
pub use workflow_title::TitleService;

pub struct Service;

#[async_trait::async_trait]
pub trait PromptService: Send + Sync {
    /// Generate prompt from a ChatRequest
    async fn get(&self, request: &forge_domain::ChatRequest) -> anyhow::Result<String>;
}