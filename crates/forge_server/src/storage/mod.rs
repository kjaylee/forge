use async_trait::async_trait;
use serde::de::DeserializeOwned;
use serde::Serialize;

mod sqlite;

pub use sqlite::SqliteStorage;

#[async_trait]
pub trait Storage: Send + Sync + std::fmt::Debug {
    /// Initialize the storage
    async fn init(&self) -> Result<(), StorageError>;

    /// Store an item and return its UUID
    async fn save<T>(&self, key: &str, item: &T) -> Result<(), StorageError>
    where
        T: Serialize + Send + Sync;

    /// Retrieve an item by its UUID
    async fn get<T>(&self, key: &str) -> Result<Option<T>, StorageError>
    where
        T: DeserializeOwned + Send + Sync;

    /// List all items
    async fn list<T>(&self) -> Result<Vec<T>, StorageError>
    where
        T: DeserializeOwned + Send + Sync;
}

#[derive(Debug, thiserror::Error)]
pub enum StorageError {
    #[error("Database error: {0}")]
    Database(#[from] sqlx::Error),

    #[error("Serialization error: {0}")]
    Serialization(#[from] serde_json::Error),

    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}
