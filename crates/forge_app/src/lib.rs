mod app;
mod provider;
mod tool_service;

use std::path::Path;

pub use app::*;
use forge_domain::WorkflowRepository;

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

pub trait Infrastructure: Send + Sync + 'static {
    type EnvironmentService: EnvironmentService;
    type FileReadService: FileReadService;
    type WorkflowRepository: WorkflowRepository;

    fn environment_service(&self) -> &Self::EnvironmentService;
    fn file_read_service(&self) -> &Self::FileReadService;
    fn workflow_repository(&self) -> &Self::WorkflowRepository;
}
