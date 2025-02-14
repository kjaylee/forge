mod app;
mod knowledge;
mod conversation;
mod provider;
mod tool_service;

use std::path::Path;

pub use app::*;
use forge_domain::Knowledge;

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
    async fn insert(&self, content: &str, embedding: &[f32]) -> anyhow::Result<()>;
    async fn search(&self, embedding: Vec<f32>) -> anyhow::Result<Vec<Knowledge>>;
    async fn list(&self) -> anyhow::Result<Vec<Knowledge>>;
}

pub trait Infrastructure: Send + Sync + 'static {
    type EnvironmentService: EnvironmentService;
    type FileReadService: FileReadService;
    type InformationRepository: InformationRepository;

    fn environment_service(&self) -> &Self::EnvironmentService;
    fn file_read_service(&self) -> &Self::FileReadService;
    fn information_repo(&self) -> &Self::InformationRepository;
}
