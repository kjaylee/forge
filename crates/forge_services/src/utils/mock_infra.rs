use std::path::{Path, PathBuf};
use std::process::ExitStatus;

use anyhow::Result;
use bytes::Bytes;
use derive_builder::Builder;
use forge_domain::{
    CommandOutput, Environment, EnvironmentService, McpServerConfig, ToolDefinition, ToolName,
    ToolOutput,
};
use forge_snaps::Snapshot;

use crate::{
    CommandExecutorService, FileRemoveService, FsCreateDirsService, FsMetaService, FsReadService,
    FsSnapshotService, FsWriteService, Infrastructure, InquireService, McpClient, McpServer,
};

#[derive(Clone, Builder)]
pub struct MockInfrastructure {}

impl Infrastructure for MockInfrastructure {
    type EnvironmentService = MockInfrastructure;
    type FsMetaService = MockInfrastructure;
    type FsReadService = MockInfrastructure;
    type FsRemoveService = MockInfrastructure;
    type FsSnapshotService = MockInfrastructure;
    type FsWriteService = MockInfrastructure;
    type FsCreateDirsService = MockInfrastructure;
    type CommandExecutorService = MockInfrastructure;
    type InquireService = MockInfrastructure;
    type McpServer = MockInfrastructure;

    fn environment_service(&self) -> &Self::EnvironmentService {
        self
    }

    fn file_meta_service(&self) -> &Self::FsMetaService {
        self
    }

    fn file_read_service(&self) -> &Self::FsReadService {
        self
    }

    fn file_remove_service(&self) -> &Self::FsRemoveService {
        self
    }

    fn file_snapshot_service(&self) -> &Self::FsSnapshotService {
        self
    }

    fn file_write_service(&self) -> &Self::FsWriteService {
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

    fn mcp_server(&self) -> &Self::McpServer {
        self
    }
}

impl EnvironmentService for MockInfrastructure {
    fn get_environment(&self) -> Environment {
        todo!()
    }
}

#[async_trait::async_trait]
impl FsMetaService for MockInfrastructure {
    async fn is_file(&self, _path: &Path) -> anyhow::Result<bool> {
        todo!()
    }

    async fn exists(&self, _path: &Path) -> anyhow::Result<bool> {
        todo!()
    }
}

#[async_trait::async_trait]
impl FsReadService for MockInfrastructure {
    async fn read_utf8(&self, _path: &Path) -> anyhow::Result<String> {
        todo!()
    }

    async fn read(&self, _path: &Path) -> anyhow::Result<Vec<u8>> {
        todo!()
    }

    async fn range_read_utf8(
        &self,
        _path: &Path,
        _start_char: u64,
        _end_char: u64,
    ) -> anyhow::Result<(String, forge_fs::FileInfo)> {
        todo!()
    }
}

#[async_trait::async_trait]
impl FileRemoveService for MockInfrastructure {
    async fn remove(&self, _path: &Path) -> anyhow::Result<()> {
        todo!()
    }
}

#[async_trait::async_trait]
impl FsSnapshotService for MockInfrastructure {
    async fn create_snapshot(&self, _file_path: &Path) -> Result<Snapshot> {
        todo!()
    }

    async fn undo_snapshot(&self, _file_path: &Path) -> Result<()> {
        todo!()
    }
}

#[async_trait::async_trait]
impl FsWriteService for MockInfrastructure {
    async fn write(&self, _path: &Path, _contents: Bytes) -> anyhow::Result<()> {
        todo!()
    }

    async fn write_temp(
        &self,
        _prefix: &str,
        _ext: &str,
        _content: &str,
    ) -> anyhow::Result<PathBuf> {
        todo!()
    }
}

#[async_trait::async_trait]
impl FsCreateDirsService for MockInfrastructure {
    async fn create_dirs(&self, _path: &Path) -> anyhow::Result<()> {
        todo!()
    }
}

#[async_trait::async_trait]
impl CommandExecutorService for MockInfrastructure {
    async fn execute_command(
        &self,
        _command: String,
        _working_dir: PathBuf,
    ) -> anyhow::Result<CommandOutput> {
        todo!()
    }

    async fn execute_command_raw(
        &self,
        _command: &str,
        _args: &[&str],
    ) -> anyhow::Result<ExitStatus> {
        todo!()
    }
}

#[async_trait::async_trait]
impl InquireService for MockInfrastructure {
    async fn prompt_question(&self, _question: &str) -> anyhow::Result<Option<String>> {
        todo!()
    }

    async fn select_one(
        &self,
        _message: &str,
        _options: Vec<String>,
    ) -> anyhow::Result<Option<String>> {
        todo!()
    }

    async fn select_many(
        &self,
        _message: &str,
        _options: Vec<String>,
    ) -> anyhow::Result<Option<Vec<String>>> {
        todo!()
    }
}

pub struct MockMcpClient;

#[async_trait::async_trait]
impl McpClient for MockMcpClient {
    async fn list(&self) -> anyhow::Result<Vec<ToolDefinition>> {
        todo!()
    }

    async fn call(
        &self,
        _tool_name: &ToolName,
        _input: serde_json::Value,
    ) -> anyhow::Result<ToolOutput> {
        todo!()
    }
}

#[async_trait::async_trait]
impl McpServer for MockInfrastructure {
    type Client = MockMcpClient;

    async fn connect(&self, _config: McpServerConfig) -> anyhow::Result<Self::Client> {
        todo!()
    }
}
