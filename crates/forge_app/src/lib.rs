mod app;
mod conversation;
mod knowledge;
mod provider;
mod tool_service;

use std::path::Path;

pub use app::*;
use forge_domain::{Knowledge, KnowledgeId};
use serde_json::Value;
use uuid::Uuid;

/// Repository for accessing system environment information
#[async_trait::async_trait]
pub trait EnvironmentService {
    /// Get the current environment information including:
    /// - Operating system
    /// - Current working directory
    /// - Home directory
    /// - Default shell
    fn get_environment(&self) -> forge_domain::Environment;
}

/// A service for reading files from the filesystem.
///
/// This trait provides an abstraction over file reading operations, allowing
/// for both real file system access and test mocking.
#[async_trait::async_trait]
pub trait FileReadService: Send + Sync {
    /// Reads the content of a file at the specified path.
    async fn read(&self, path: &Path) -> anyhow::Result<String>;
}

#[async_trait::async_trait]
pub trait InformationRepository: Send + Sync {
    type Value;
    async fn upsert(&self, information: Vec<Knowledge<Self::Value>>) -> anyhow::Result<()>;
    async fn drop(&self, ids: Vec<KnowledgeId>) -> anyhow::Result<()>;
    async fn search(&self, embedding: Vec<f32>) -> anyhow::Result<Vec<Knowledge<Self::Value>>>;
    async fn list(&self) -> anyhow::Result<Vec<Knowledge<Self::Value>>>;
}

pub trait Infrastructure: Send + Sync + 'static {
    type EnvironmentService: EnvironmentService;
    type FileReadService: FileReadService;
    type InformationRepository: InformationRepository;

    fn environment_service(&self) -> &Self::EnvironmentService;
    fn file_read_service(&self) -> &Self::FileReadService;
    fn textual_knowledge_repo(&self) -> &Self::InformationRepository;
}
