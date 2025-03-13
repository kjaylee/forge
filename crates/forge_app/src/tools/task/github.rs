use std::process::Command;

use anyhow::{anyhow, Result};
use forge_domain::*;
use serde::Deserialize;

use crate::tools::shell::*;

#[derive(Debug, Deserialize)]
pub struct IssueDetails {
    pub title: String,
    pub body: String,
    pub url: String,
    #[allow(dead_code)]
    pub author: GithubUser,
    #[allow(dead_code)]
    pub labels: Vec<GithubLabel>,
}

#[derive(Debug, Deserialize)]
pub struct GithubUser {
    pub login: String,
    #[serde(default)]
    pub name: Option<String>,
    #[serde(default, rename = "is_bot")]
    pub is_bot: Option<bool>,
    #[serde(default)]
    pub id: Option<String>,
}

#[derive(Debug, Deserialize)]
pub struct GithubLabel {
    #[serde(default)]
    pub name: String,
    #[serde(default)]
    pub color: Option<String>,
    #[serde(default)]
    pub description: Option<String>,
}

#[derive(Debug, Deserialize)]
pub struct Comment {
    pub body: String,
    pub author: GithubUser,
    #[serde(rename = "createdAt")]
    pub created_at: String,
}

/// GitHub API client that uses gh CLI commands via shell
pub struct GithubClient {
    shell: Shell,
}

impl GithubClient {
    pub fn new(env: Environment) -> Self {
        Self { shell: Shell::new(env) }
    }

    /// Fetches details of a GitHub issue using direct command execution
    pub async fn get_issue_details(&self, issue_number: u32) -> Result<IssueDetails> {
        // Execute the gh CLI command directly
        let output = Command::new("gh")
            .args([
                "issue",
                "view",
                &issue_number.to_string(),
                "--json",
                "title,body,url,author,labels",
            ])
            .output()
            .map_err(|e| anyhow!("Failed to execute GitHub CLI: {}", e))?;

        if !output.status.success() {
            return Err(anyhow!(
                "GitHub command failed: {}",
                String::from_utf8_lossy(&output.stderr)
            ));
        }

        let json_content = String::from_utf8_lossy(&output.stdout).to_string();

        // For debugging
        println!("JSON from direct command: {}", json_content);

        let issue: IssueDetails = serde_json::from_str(&json_content).map_err(|e| {
            anyhow!(
                "Failed to parse issue details: {}\nJSON: {}",
                e,
                json_content
            )
        })?;

        Ok(issue)
    }

    /// Creates a branch for the issue or uses an existing one if it already
    /// exists
    pub async fn create_branch_for_issue(&self, issue_number: u32) -> Result<String> {
        let branch_name = format!("fix/issue-{}", issue_number);

        // First check if the branch already exists
        let check_output = Command::new("git")
            .args(&["branch", "--list", &branch_name])
            .output()
            .map_err(|e| anyhow!("Failed to check for existing branch: {}", e))?;

        let branch_exists = String::from_utf8_lossy(&check_output.stdout).contains(&branch_name);

        if branch_exists {
            println!("Branch {} already exists, using it", branch_name);

            // Checkout the existing branch
            let checkout_output = Command::new("git")
                .args(&["checkout", &branch_name])
                .output()
                .map_err(|e| anyhow!("Failed to checkout existing branch: {}", e))?;

            if !checkout_output.status.success() {
                return Err(anyhow!(
                    "Failed to checkout existing branch: {}",
                    String::from_utf8_lossy(&checkout_output.stderr)
                ));
            }
        } else {
            // Create and checkout a new branch
            let output = Command::new("git")
                .args(["checkout", "-b", &branch_name])
                .output()
                .map_err(|e| anyhow!("Failed to create branch: {}", e))?;

            if !output.status.success() {
                return Err(anyhow!(
                    "Git command failed: {}",
                    String::from_utf8_lossy(&output.stderr)
                ));
            }
        }

        Ok(branch_name)
    }

    /// Creates a draft PR for the issue or returns existing PR if one exists
    /// for the branch
    pub async fn create_draft_pr(&self, title: &str, body: &str, branch: &str) -> Result<u32> {
        // Execute gh CLI directly
        let output = Command::new("gh")
            .args(&[
                "pr", "create", "--draft", "--title", title, "--body", body, "--head", branch,
            ])
            .output()
            .map_err(|e| anyhow!("Failed to create PR: {}", e))?;

        if !output.status.success() {
            return Err(anyhow!(
                "GitHub PR command failed: {}",
                String::from_utf8_lossy(&output.stderr)
            ));
        }

        let pr_url = String::from_utf8_lossy(&output.stdout).trim().to_string();

        // Extract PR number from the URL
        // The output is typically like: https://github.com/owner/repo/pull/123
        let pr_number = pr_url
            .split('/')
            .next_back()
            .and_then(|s| s.parse::<u32>().ok())
            .ok_or_else(|| anyhow!("Failed to extract PR number from URL: {}", pr_url))?;

        Ok(pr_number)
    }

    /// Fetches comments from a PR
    pub async fn get_pr_comments(&self, pr_number: u32) -> Result<Vec<Comment>> {
        // Execute gh CLI directly
        let output = Command::new("gh")
            .args([
                "pr",
                "view",
                &pr_number.to_string(),
                "--json",
                "comments",
                "--jq",
                ".comments[]",
            ])
            .output()
            .map_err(|e| anyhow!("Failed to fetch PR comments: {}", e))?;

        if !output.status.success() {
            return Err(anyhow!(
                "GitHub PR comments command failed: {}",
                String::from_utf8_lossy(&output.stderr)
            ));
        }

        let content = String::from_utf8_lossy(&output.stdout).to_string();

        if content.trim().is_empty() {
            return Ok(vec![]);
        }

        // Parse the comments from the JSON output
        let comments: Vec<Comment> = serde_json::from_str(&format!("[{}]", content))
            .map_err(|e| anyhow!("Failed to parse comments: {}\nContent: {}", e, content))?;

        Ok(comments)
    }
}
