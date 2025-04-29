use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub struct Suggestion {
    pub use_case: String,
    pub suggestion: String,
}

#[async_trait::async_trait]
pub trait SuggestionService: Send + Sync {
    async fn suggestions(&self) -> anyhow::Result<Vec<crate::File>>;
}
