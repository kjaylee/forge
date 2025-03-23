mod bug_reporter;
mod comment_file;
mod comment_pr;
mod model;
mod review_workflow;
mod rule_based;
mod summarizer;

pub use model::*;
pub use review_workflow::ReviewWorkflow;

#[async_trait::async_trait]
pub trait SummaryAgent {
    async fn summarize(&self) -> anyhow::Result<String>;
}
