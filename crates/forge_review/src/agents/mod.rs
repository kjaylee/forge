mod architect;
mod bug_reporter;
mod code_smell;
mod summarizer;

pub use code_smell::CodeSmellAgent;
pub use architect::ArchitectureAgent;
pub use bug_reporter::BugReporterAgent;
pub use summarizer::CombineSummaryAgent;

#[async_trait::async_trait]
pub trait SummaryAgent {
    async fn summarize(&self) -> anyhow::Result<String>;
}
