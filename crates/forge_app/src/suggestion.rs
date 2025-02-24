use std::sync::Arc;

use anyhow::Result;
use async_trait::async_trait;
use forge_domain::{ChatRequest, Suggestion, SuggestionService};
use tracing::instrument;

use crate::Infrastructure;

pub struct ForgeSuggestionService<F> {
    infra: Arc<F>,
}

impl<F: Infrastructure> ForgeSuggestionService<F> {
    pub fn new(infra: Arc<F>) -> Self {
        Self { infra }
    }
}

#[async_trait]
impl<F: Infrastructure> SuggestionService for ForgeSuggestionService<F> {
    #[instrument(skip(self))]
    async fn search(&self, request: ChatRequest) -> Result<Vec<Suggestion>> {
        todo!()
    }

    async fn insert(&self, request: ChatRequest, suggestion: Suggestion) -> Result<()> {
        todo!()
    }
}
