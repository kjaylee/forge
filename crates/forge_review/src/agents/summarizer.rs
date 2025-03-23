use std::sync::Arc;

use crate::domain::PullRequest;

use super::SummaryAgent;

pub struct CombineSummaryAgent {
    review: Arc<PullRequest>,
    summary: Vec<String>,
}

impl CombineSummaryAgent {
    pub fn new(review: Arc<PullRequest>, summary: Vec<String>) -> Self {
        Self { review, summary }
    }
}

#[async_trait::async_trait]
impl SummaryAgent for CombineSummaryAgent {
    async fn summarize(&self) -> anyhow::Result<String> {
        todo!()
    }
}