use std::path::PathBuf;

use serde::{Deserialize, Serialize};

/// Defines the configuration for fixing an issue
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FixIssueConfig {
    /// GitHub issue number to fix
    pub issue: u32,
    /// Minimum number of proposals to generate
    #[serde(default = "default_min_proposals")]
    pub min_proposals: u32,
    /// Optional custom title for the PR
    #[serde(skip_serializing_if = "Option::is_none")]
    pub title: Option<String>,
}

/// Defines the configuration for updating a PR
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UpdatePrConfig {
    /// GitHub PR number to update
    pub pr: u32,
}

/// Represents the task operations that can be dispatched
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TaskDispatchConfig {
    /// Configuration for fixing an issue
    #[serde(skip_serializing_if = "Option::is_none")]
    pub fix_issue: Option<FixIssueConfig>,
    /// Configuration for updating a PR
    #[serde(skip_serializing_if = "Option::is_none")]
    pub update_pr: Option<UpdatePrConfig>,
}

/// Represents the status of a task
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum TaskStatus {
    /// Task is planned but not started
    Planned,
    /// Task is in progress
    InProgress,
    /// Task is completed
    Completed,
    /// Task has failed
    Failed(String),
}

fn default_min_proposals() -> u32 {
    3
}

/// Service for managing task files and GitHub integrations
#[async_trait::async_trait]
pub trait TaskService: Send + Sync {
    /// Create a task file for fixing an issue
    async fn create_issue_task(&self, config: &FixIssueConfig) -> anyhow::Result<PathBuf>;

    /// Update a task based on PR comments
    async fn update_task(&self, config: &UpdatePrConfig) -> anyhow::Result<()>;

    /// Parse a dispatch JSON string into a TaskDispatchConfig
    fn parse_dispatch_config(&self, json: &str) -> anyhow::Result<TaskDispatchConfig>;
}
