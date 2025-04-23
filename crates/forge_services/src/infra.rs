use std::path::{Path, PathBuf};

use anyhow::Result;
use bytes::Bytes;
use forge_domain::{CommandOutput, EnvironmentService};
use forge_snaps::Snapshot;

/// Repository for accessing system environment information
/// This uses the EnvironmentService trait from forge_domain
/// A service for reading files from the filesystem.
///
/// This trait provides an abstraction over file reading operations, allowing
/// for both real file system access and test mocking.
#[async_trait::async_trait]
pub trait FsReadService: Send + Sync {
    /// Reads the content of a file at the specified path.
    async fn read(&self, path: &Path) -> anyhow::Result<Bytes>;
}

#[async_trait::async_trait]
pub trait FsWriteService: Send + Sync {
    /// Writes the content of a file at the specified path.
    async fn write(&self, path: &Path, contents: Bytes) -> anyhow::Result<()>;
}

#[async_trait::async_trait]
pub trait FsRemoveService: Send + Sync {
    /// Removes a file at the specified path.
    async fn remove(&self, path: &Path) -> anyhow::Result<()>;
}

#[async_trait::async_trait]
pub trait FsMetaService: Send + Sync {
    async fn is_file(&self, path: &Path) -> anyhow::Result<bool>;
    async fn exists(&self, path: &Path) -> anyhow::Result<bool>;
}

#[async_trait::async_trait]
pub trait FsCreateDirsService: Send + Sync {
    async fn create_dirs(&self, path: &Path) -> anyhow::Result<()>;
}

/// Service for managing file snapshots
#[async_trait::async_trait]
pub trait FsSnapshotService: Send + Sync {
    // Creation
    async fn create_snapshot(&self, file_path: &Path) -> Result<Snapshot>;

    /// Restores the most recent snapshot for the given file path
    async fn undo_snapshot(&self, file_path: &Path) -> Result<()>;
}

/// Service for executing shell commands
#[async_trait::async_trait]
pub trait CommandExecutorService: Send + Sync {
    /// Executes a shell command and returns the output
    async fn execute_command(
        &self,
        command: String,
        working_dir: PathBuf,
    ) -> anyhow::Result<CommandOutput>;
}

/// Service for interactive selection
#[async_trait::async_trait]
pub trait InquireService: Send + Sync {
    /// Prompts the user to select a single option from a list
    async fn select_one(&self, message: &str, options: Vec<String>) -> anyhow::Result<String>;

    /// Prompts the user to select multiple options from a list
    async fn select_many(&self, message: &str, options: Vec<String>)
        -> anyhow::Result<Vec<String>>;
}

pub trait Infrastructure: Send + Sync + Clone + 'static {
    type EnvironmentService: EnvironmentService;
    type FsMetaService: FsMetaService;
    type FsReadService: FsReadService;
    type FsRemoveService: FsRemoveService;
    type FsSnapshotService: FsSnapshotService;
    type FsWriteService: FsWriteService;
    type FsCreateDirsService: FsCreateDirsService;
    type CommandExecutorService: CommandExecutorService;
    type InquireService: InquireService;

    fn environment_service(&self) -> &Self::EnvironmentService;
    fn file_meta_service(&self) -> &Self::FsMetaService;
    fn file_read_service(&self) -> &Self::FsReadService;
    fn file_remove_service(&self) -> &Self::FsRemoveService;
    fn file_snapshot_service(&self) -> &Self::FsSnapshotService;
    fn file_write_service(&self) -> &Self::FsWriteService;
    fn create_dirs_service(&self) -> &Self::FsCreateDirsService;
    fn command_executor_service(&self) -> &Self::CommandExecutorService;
    fn inquire_service(&self) -> &Self::InquireService;
}

#[cfg(test)]
pub mod stub {

    use forge_domain::{Environment, EnvironmentService, Provider};

    use super::*;

    impl Default for Stub {
        fn default() -> Self {
            Stub {
                env: Environment {
                    os: std::env::consts::OS.to_string(),
                    cwd: std::env::current_dir().unwrap_or_default(),
                    home: Some("/".into()),
                    shell: if cfg!(windows) {
                        "cmd.exe".to_string()
                    } else {
                        "/bin/sh".to_string()
                    },
                    base_path: PathBuf::new(),
                    pid: std::process::id(),
                    provider: Provider::anthropic("test-key"),
                    retry_config: Default::default(),
                },
            }
        }
    }

    #[derive(Clone)]
    pub struct Stub {
        env: Environment,
    }

    #[async_trait::async_trait]
    impl EnvironmentService for Stub {
        fn get_environment(&self) -> Environment {
            self.env.clone()
        }
    }

    #[async_trait::async_trait]
    impl FsReadService for Stub {
        async fn read(&self, _path: &Path) -> anyhow::Result<Bytes> {
            unimplemented!()
        }
    }

    #[async_trait::async_trait]
    impl FsWriteService for Stub {
        async fn write(&self, _: &Path, _: Bytes) -> anyhow::Result<()> {
            unimplemented!()
        }
    }

    #[async_trait::async_trait]
    impl FsSnapshotService for Stub {
        async fn create_snapshot(&self, _: &Path) -> anyhow::Result<Snapshot> {
            unimplemented!()
        }

        async fn undo_snapshot(&self, _: &Path) -> anyhow::Result<()> {
            Ok(())
        }
    }

    #[async_trait::async_trait]
    impl FsMetaService for Stub {
        async fn is_file(&self, _: &Path) -> anyhow::Result<bool> {
            unimplemented!()
        }

        async fn exists(&self, _: &Path) -> anyhow::Result<bool> {
            unimplemented!()
        }
    }

    #[async_trait::async_trait]
    impl FsRemoveService for Stub {
        async fn remove(&self, _: &Path) -> anyhow::Result<()> {
            unimplemented!()
        }
    }

    #[async_trait::async_trait]
    impl FsCreateDirsService for Stub {
        async fn create_dirs(&self, _: &Path) -> anyhow::Result<()> {
            unimplemented!()
        }
    }

    #[async_trait::async_trait]
    impl CommandExecutorService for Stub {
        async fn execute_command(&self, _: String, _: PathBuf) -> anyhow::Result<CommandOutput> {
            unimplemented!()
        }
    }

    #[async_trait::async_trait]
    impl InquireService for Stub {
        async fn select_one(&self, _: &str, _: Vec<String>) -> anyhow::Result<String> {
            unimplemented!()
        }

        async fn select_many(&self, _: &str, _: Vec<String>) -> anyhow::Result<Vec<String>> {
            unimplemented!()
        }
    }

    #[async_trait::async_trait]
    impl Infrastructure for Stub {
        type EnvironmentService = Stub;
        type FsReadService = Stub;
        type FsWriteService = Stub;
        type FsRemoveService = Stub;
        type FsMetaService = Stub;
        type FsSnapshotService = Stub;
        type FsCreateDirsService = Stub;
        type CommandExecutorService = Stub;
        type InquireService = Stub;

        fn environment_service(&self) -> &Self::EnvironmentService {
            self
        }

        fn file_read_service(&self) -> &Self::FsReadService {
            self
        }

        fn file_write_service(&self) -> &Self::FsWriteService {
            self
        }

        fn file_meta_service(&self) -> &Self::FsMetaService {
            self
        }

        fn file_snapshot_service(&self) -> &Self::FsSnapshotService {
            self
        }

        fn file_remove_service(&self) -> &Self::FsRemoveService {
            self
        }

        fn create_dirs_service(&self) -> &Self::FsCreateDirsService {
            self
        }

        fn command_executor_service(&self) -> &Self::CommandExecutorService {
            self
        }

        fn inquire_service(&self) -> &Self::InquireService {
            self
        }
    }
}
