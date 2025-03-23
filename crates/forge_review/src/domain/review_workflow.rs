use std::path::PathBuf;
use std::sync::Arc;

use anyhow::Result;
use futures::future::join_all;

use super::SummaryAgent;
use super::architect::ArchitectureAgent;
use super::bug_reporter::BugReporterAgent;
use super::code_smell::CodeSmellAgent;
use super::summarizer::CombineSummaryAgent;
// Import all the agents
use crate::{
    domain::PullRequest,
    github::{GithubFileCommentator, GithubPRCommentator},
    infra::{GithubAPI, ReviewInfrastructure},
};

#[derive(Clone)]
pub struct ReviewWorkflow<I> {
    infra: Arc<I>,
}

impl<I: ReviewInfrastructure> ReviewWorkflow<I> {
    pub fn new(infra: Arc<I>) -> Self {
        Self { infra }
    }

    pub async fn review_each_file(
        &self,
        pull_request: Arc<PullRequest>,
        file: PathBuf,
    ) -> Result<String> {
        // Create agents for file-specific reviews
        let agents: Vec<Box<dyn SummaryAgent>> = vec![
            Box::new(CodeSmellAgent::new(pull_request.clone(), file.clone())),
            Box::new(ArchitectureAgent::new(
                pull_request.clone(),
                file.clone(),
                self.infra.clone(),
            )),
        ];

        // Execute all futures concurrently
        let results = join_all(
            agents
                .into_iter()
                .map(|agent| async move { agent.summarize().await }),
        )
        .await
        .into_iter()
        .collect::<Result<Vec<_>>>()?;

        // Combine all the comments
        let combiner = CombineSummaryAgent::new(pull_request, results);
        combiner.summarize().await
    }

    pub async fn review_complete_pr(&self, review: Arc<PullRequest>) -> Result<()> {
        let bug_reporter = BugReporterAgent::new(review.clone());
        let comments = bug_reporter.summarize().await?;

        let commentator = GithubPRCommentator::new(comments);
        commentator.comment().await
    }

    pub async fn run(&self) -> Result<()> {
        let pull_request: Arc<PullRequest> =
            Arc::new(self.infra.github_api().get_pull_request().await?);
        let modified_files = pull_request.modified_files();

        // Run file reviews in parallel using futures::future::join_all
        let file_feedback = self
            .generate_file_feedback(&pull_request, modified_files)
            .await?;

        // Create and use GithubFileCommentator to post feedback for all files.
        let commentator = GithubFileCommentator::new(file_feedback);
        commentator.comment().await?;

        self.review_complete_pr(pull_request.clone()).await?;

        Ok(())
    }

    async fn generate_file_feedback(
        &self,
        pull_request: &Arc<PullRequest>,
        modified_files: Vec<String>,
    ) -> Result<Vec<(PathBuf, String)>, anyhow::Error> {
        join_all(modified_files.into_iter().map(|file_path| async {
            let file = PathBuf::from(file_path);
            let pull_request_clone = pull_request.clone();

            let summary = self
                .review_each_file(pull_request_clone, file.clone())
                .await?;
            Ok::<_, anyhow::Error>((file, summary))
        }))
        .await
        .into_iter()
        .collect::<Result<Vec<_>>>()
    }
}
