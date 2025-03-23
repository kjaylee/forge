use std::{path::PathBuf, sync::Arc};

use crate::domain::PullRequest;

use super::SummaryAgent;

pub struct BugReporterAgent {
    review: Arc<PullRequest>,
    file: PathBuf,
}

impl BugReporterAgent {
    pub fn new(review: Arc<PullRequest>, file: PathBuf) -> Self {
        Self { review, file }
    }
}

#[async_trait::async_trait]
impl SummaryAgent for BugReporterAgent {
    async fn summarize(&self) -> anyhow::Result<String> {
        todo!()
    }
}