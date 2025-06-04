use std::path::Path;
use std::pin::Pin;

use async_jsonl::JsonlDeserialize;
use forge_domain::{Buffer, JsonlIterator};
use forge_services::BufferService;
use futures::{Stream, StreamExt};
use tokio::fs::{File, OpenOptions};
use tokio::io::AsyncWriteExt;

pub struct ForgeBufferService {}

impl Default for ForgeBufferService {
    fn default() -> Self {
        Self::new()
    }
}

impl ForgeBufferService {
    pub fn new() -> Self {
        Self {}
    }
    async fn file(&self, path: &Path) -> anyhow::Result<File> {
        Ok(OpenOptions::new()
            .append(true)
            .create(true)
            .open(path)
            .await?)
    }
    async fn write(&self, path: &Path, buffer: Buffer) -> anyhow::Result<()> {
        let mut string = serde_json::to_string(&buffer)?;
        string.push('\n');
        self.file(path).await?.write_all(string.as_bytes()).await?;
        Ok(())
    }
}

#[async_trait::async_trait]
impl BufferService for ForgeBufferService {
    async fn read(&self, path: &Path) -> anyhow::Result<JsonlIterator> {
        let file = File::open(path)
            .await
            .map_err(|e| anyhow::anyhow!("Failed to open file: {}", e))?;
        let iter = async_jsonl::Jsonl::new(file).deserialize::<Buffer>();
        let stream: Pin<Box<dyn Stream<Item = Buffer> + Send + Sync>> =
            Box::pin(futures::stream::unfold(iter, |mut iter| async move {
                let buffer = StreamExt::next(&mut iter).await.and_then(|v| v.ok())?;
                Some((buffer, iter))
            }));
        Ok(JsonlIterator::new(stream))
    }

    async fn write(&self, path: &Path, buffer: Buffer) -> anyhow::Result<()> {
        self.write(path, buffer).await
    }
}
