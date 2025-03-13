use std::path::PathBuf;
use std::sync::Arc;

use anyhow::{anyhow, Context, Result};
use forge_domain::{
    Environment, ExecutableTool, FixIssueConfig, TaskDispatchConfig, TaskService, TaskStatus,
    UpdatePrConfig,
};

use super::github::GithubClient;
use super::task_file::TaskFile;
use crate::tools::shell::*;
use crate::{EnvironmentService, Infrastructure};

pub struct ForgeTaskService<F> {
    infra: Arc<F>,
}

impl<F: Infrastructure> ForgeTaskService<F> {
    pub fn new(infra: Arc<F>) -> Self {
        Self { infra }
    }

    fn get_environment(&self) -> Environment {
        self.infra.environment_service().get_environment()
    }
}

#[async_trait::async_trait]
impl<F: Infrastructure> TaskService for ForgeTaskService<F> {
    async fn create_issue_task(&self, config: &FixIssueConfig) -> Result<PathBuf> {
        let env = self.get_environment();

        // Create GitHub client
        let github = GithubClient::new(env.clone());

        // Fetch issue details
        let issue = github
            .get_issue_details(config.issue)
            .await
            .context(format!("Failed to fetch issue #{}", config.issue))?;

        // Create a branch for the issue
        let branch = github
            .create_branch_for_issue(config.issue)
            .await
            .context("Failed to create branch")?;

        // Create task file
        let task_path = TaskFile::create_for_issue(
            config.issue,
            &issue.title,
            &issue.url,
            &issue.body,
            config.min_proposals,
            config.title.as_deref(),
        )
        .await
        .context("Failed to create task file")?;

        // Create a commit with the task file
        let shell_service = Shell::new(env);

        // Add and commit the task file
        let input = ShellInput {
            command: format!(
                "git add {} && git commit -m \"Create task for issue #{}\"",
                task_path.display(),
                config.issue
            ),
            cwd: std::env::current_dir()?,
        };

        shell_service.call(input).await?;

        // Create a draft PR
        let pr_body = format!(
            "This PR addresses issue #{}\n\n\
            ## Task\n\n\
            See the `.task.md` file for details.\n",
            config.issue
        );

        let pr_title = config
            .title
            .clone()
            .unwrap_or_else(|| format!("Fix issue #{}", config.issue));

        let pr_number = github
            .create_draft_pr(&pr_title, &pr_body, &branch)
            .await
            .context("Failed to create draft PR")?;

        // Update the task file with the PR number
        TaskFile::update(
            pr_number,
            &task_path,
            Vec::new(), // No comments yet
            TaskStatus::InProgress,
        )
        .await
        .context("Failed to update task file with PR number")?;

        // Commit the updated task file
        let input = ShellInput {
            command: format!(
                "git add {} && git commit -m \"Update task status for PR #{}\"",
                task_path.display(),
                pr_number
            ),
            cwd: std::env::current_dir()?,
        };

        shell_service.call(input).await?;

        // Push the branch
        let input = ShellInput {
            command: format!("git push --set-upstream origin {}", branch),
            cwd: std::env::current_dir()?,
        };

        shell_service.call(input).await?;

        Ok(task_path)
    }

    async fn update_task(&self, config: &UpdatePrConfig) -> Result<()> {
        let env = self.get_environment();
        let github = GithubClient::new(env);

        // Find the task file
        let task_path = PathBuf::from(".task.md");
        if !task_path.exists() {
            return Err(anyhow!("Task file not found: {}", task_path.display()));
        }

        // Fetch PR comments
        let comments = github
            .get_pr_comments(config.pr)
            .await
            .context(format!("Failed to fetch comments for PR #{}", config.pr))?;

        // Convert comments to the format expected by TaskFile::update
        let formatted_comments = comments
            .into_iter()
            .map(|c| (c.author.login, c.created_at, c.body))
            .collect();

        // Update the task file
        TaskFile::update(
            config.pr,
            &task_path,
            formatted_comments,
            TaskStatus::InProgress, // Default to InProgress, could be more sophisticated
        )
        .await
        .context("Failed to update task file")?;

        Ok(())
    }

    fn parse_dispatch_config(&self, json: &str) -> Result<TaskDispatchConfig> {
        serde_json::from_str(json).context("Failed to parse dispatch config JSON")
    }
}
