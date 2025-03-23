mod architect;
mod bug_reporter;
mod code_smell;
mod comment_file;
mod comment_pr;
mod review_workflow;
mod summarizer;

pub use review_workflow::ReviewWorkflow;

#[async_trait::async_trait]
pub trait SummaryAgent {
    async fn summarize(&self) -> anyhow::Result<String>;
}
