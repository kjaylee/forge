use std::sync::Arc;


use super::{PullRequest, SummaryAgent};

pub struct ArchitectureAgent {
    review: Arc<PullRequest>,
}

impl ArchitectureAgent {
    pub fn new(review: Arc<PullRequest>) -> Self {
        Self { review }
    }
}

#[async_trait::async_trait]
impl SummaryAgent for ArchitectureAgent {
    async fn summarize(&self) -> anyhow::Result<String> {
        todo!()
    }
}