use std::sync::Arc;

use bytes::Bytes;
use forge_app::{AppConfig, AppConfigService};

use crate::{EnvironmentInfra, FileDirectoryInfra, FileReaderInfra, FileWriterInfra};

pub struct ForgeConfigService<I> {
    infra: Arc<I>,
}

impl<I: FileReaderInfra + FileWriterInfra + EnvironmentInfra + FileDirectoryInfra>
    ForgeConfigService<I>
{
    pub fn new(infra: Arc<I>) -> Self {
        Self { infra }
    }
    async fn read(&self) -> anyhow::Result<AppConfig> {
        let env = self.infra.get_environment();
        let config = self.infra.read(env.app_config().as_path()).await?;
        Ok(serde_json::from_slice(&config)?)
    }
    async fn write(&self, config: &AppConfig) -> anyhow::Result<()> {
        let env = self.infra.get_environment();
        let path = env.app_config();
        if let Some(parent) = path.parent() {
            self.infra.create_dirs(parent).await?;
        }
        self.infra
            .write(
                path.as_path(),
                Bytes::from(serde_json::to_vec(config)?),
                false,
            )
            .await
    }
}

#[async_trait::async_trait]
impl<I: FileReaderInfra + FileWriterInfra + EnvironmentInfra + FileDirectoryInfra> AppConfigService
    for ForgeConfigService<I>
{
    async fn read_app_config(&self) -> anyhow::Result<AppConfig> {
        self.read().await
    }

    async fn write_app_config(&self, config: &AppConfig) -> anyhow::Result<()> {
        self.write(config).await
    }
}
