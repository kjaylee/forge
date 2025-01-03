use std::fs;

use chrono::{DateTime, NaiveDateTime, Utc};
use diesel::prelude::*;
use diesel::r2d2::{ConnectionManager, Pool};
use diesel::sql_types::{Text, Timestamp};
use diesel::sqlite::SqliteConnection;
use diesel_migrations::{embed_migrations, EmbeddedMigrations, MigrationHarness};
use forge_provider::{ModelId, Request as ProviderRequest};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

use super::Service;
use crate::schema::conversations;
use crate::Result;

pub const MIGRATIONS: EmbeddedMigrations = embed_migrations!("migrations");

type DbPool = Pool<ConnectionManager<SqliteConnection>>;

#[derive(Queryable, Selectable, Serialize, Deserialize, Debug)]
#[diesel(table_name = conversations)]
pub struct Conversation {
    pub id: Uuid,
    #[serde(with = "chrono::serde::ts_seconds")]
    pub created_at: DateTime<Utc>,
    #[serde(with = "chrono::serde::ts_seconds")]
    pub updated_at: DateTime<Utc>,
    pub content: String, // JSON serialized Request
}

#[derive(QueryableByName)]
#[diesel(table_name = conversations)]
struct RawConversation {
    #[diesel(sql_type = Text)]
    id: String,
    #[diesel(sql_type = Timestamp)]
    created_at: NaiveDateTime,
    #[diesel(sql_type = Timestamp)]
    updated_at: NaiveDateTime,
    #[diesel(sql_type = Text)]
    content: String,
}

impl From<RawConversation> for Conversation {
    fn from(raw: RawConversation) -> Self {
        Self {
            id: Uuid::parse_str(&raw.id).unwrap(),
            created_at: DateTime::from_naive_utc_and_offset(raw.created_at, Utc),
            updated_at: DateTime::from_naive_utc_and_offset(raw.updated_at, Utc),
            content: raw.content,
        }
    }
}

impl TryFrom<Conversation> for ProviderRequest {
    type Error = crate::error::Error;

    fn try_from(conv: Conversation) -> std::result::Result<Self, Self::Error> {
        serde_json::from_str(&conv.content).map_err(|e| {
            crate::error::Error::Custom(format!("Failed to deserialize request: {}", e))
        })
    }
}

#[derive(Insertable)]
#[diesel(table_name = conversations)]
pub struct NewConversation {
    pub id: String,
    pub content: String,
}

impl TryFrom<&ProviderRequest> for NewConversation {
    type Error = crate::error::Error;

    fn try_from(request: &ProviderRequest) -> std::result::Result<Self, Self::Error> {
        Ok(NewConversation {
            id: Uuid::new_v4().to_string(),
            content: serde_json::to_string(request).map_err(|e| {
                crate::error::Error::Custom(format!("Failed to serialize request: {}", e))
            })?,
        })
    }
}

#[async_trait::async_trait]
pub trait StorageService: Send + Sync {
    async fn create_conversation(&self, request: &ProviderRequest) -> Result<Conversation>;
    async fn get_request(&self, id: Uuid) -> ProviderRequest;
    async fn get_all_conversation(&self) -> Result<Vec<Conversation>>;
    async fn update_conversation(
        &self,
        id: Uuid,
        request: &ProviderRequest,
    ) -> Result<Option<Conversation>>;
}

struct Live {
    pool: DbPool,
}

impl Live {
    pub fn new(cwd: &str) -> Result<Self> {
        let db_path = format!("{}/conversations.db", cwd);

        // Create empty database file if it doesn't exist
        if !std::path::Path::new(&db_path).exists() {
            fs::write(&db_path, "").map_err(|e| crate::error::Error::Custom(e.to_string()))?;
        }

        // Run migrations first
        let mut conn = SqliteConnection::establish(&db_path)
            .map_err(|e| crate::error::Error::Custom(e.to_string()))?;
        conn.run_pending_migrations(MIGRATIONS)
            .map_err(|e| crate::error::Error::Custom(e.to_string()))?;
        drop(conn);

        // Create connection pool
        let manager = ConnectionManager::<SqliteConnection>::new(db_path);
        let pool = Pool::builder()
            .build(manager)
            .map_err(|e| crate::error::Error::Custom(e.to_string()))?;

        Ok(Self { pool })
    }

    // Private implementation method
    async fn get_conversation_impl(&self, conversation_id: Uuid) -> Result<Option<Conversation>> {
        let conn = &mut self
            .pool
            .get()
            .map_err(|e| crate::error::Error::Custom(e.to_string()))?;

        diesel::sql_query("SELECT * FROM conversations WHERE id = ? LIMIT 1")
            .bind::<Text, _>(conversation_id.to_string())
            .get_result::<RawConversation>(conn)
            .optional()
            .map(|opt| opt.map(Into::into))
            .map_err(|e| crate::error::Error::Custom(e.to_string()))
    }
}

#[async_trait::async_trait]
impl StorageService for Live {
    async fn create_conversation(&self, request: &ProviderRequest) -> Result<Conversation> {
        use crate::schema::conversations::dsl::*;

        let new_conversation = NewConversation::try_from(request)?;
        let conn = &mut self
            .pool
            .get()
            .map_err(|e| crate::error::Error::Custom(e.to_string()))?;

        diesel::insert_into(conversations)
            .values(&new_conversation)
            .execute(conn)
            .map_err(|e| crate::error::Error::Custom(e.to_string()))?;

        diesel::sql_query("SELECT * FROM conversations WHERE id = ? LIMIT 1")
            .bind::<Text, _>(new_conversation.id)
            .get_result::<RawConversation>(conn)
            .map(|raw| raw.into())
            .map_err(|e| crate::error::Error::Custom(e.to_string()))
    }

    async fn get_request(&self, id: Uuid) -> ProviderRequest {
        if let Ok(Some(conversation)) = self.get_conversation_impl(id).await {
            conversation
                .try_into()
                .unwrap_or_else(|_| ProviderRequest::new(ModelId::default()))
        } else {
            ProviderRequest::new(ModelId::default())
        }
    }

    async fn get_all_conversation(&self) -> Result<Vec<Conversation>> {
        let conn = &mut self
            .pool
            .get()
            .map_err(|e| crate::error::Error::Custom(e.to_string()))?;

        let raw_convs: Vec<RawConversation> = diesel::sql_query("SELECT * FROM conversations")
            .load(conn)
            .map_err(|e| crate::error::Error::Custom(e.to_string()))?;

        let convs: Vec<Conversation> = raw_convs.into_iter().map(Into::into).collect();

        Ok(convs)
    }

    async fn update_conversation(
        &self,
        conversation_id: Uuid,
        request: &ProviderRequest,
    ) -> Result<Option<Conversation>> {
        use crate::schema::conversations::dsl::*;

        let conn = &mut self
            .pool
            .get()
            .map_err(|e| crate::error::Error::Custom(e.to_string()))?;

        let content_str = serde_json::to_string(request).map_err(|e| {
            crate::error::Error::Custom(format!("Failed to serialize request: {}", e))
        })?;

        let now = chrono::Utc::now().naive_utc();
        let updated = diesel::update(conversations.find(conversation_id.to_string()))
            .set((content.eq(content_str), updated_at.eq(now)))
            .execute(conn)
            .map_err(|e| crate::error::Error::Custom(e.to_string()))?;

        if updated > 0 {
            diesel::sql_query("SELECT * FROM conversations WHERE id = ? LIMIT 1")
                .bind::<Text, _>(conversation_id.to_string())
                .get_result::<RawConversation>(conn)
                .optional()
                .map(|opt| opt.map(Into::into))
                .map_err(|e| crate::error::Error::Custom(e.to_string()))
        } else {
            Ok(None)
        }
    }
}

impl Service {
    pub fn storage_service(database_url: &str) -> Result<impl StorageService> {
        Live::new(database_url)
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use diesel_migrations::MigrationHarness;
    use forge_provider::CompletionMessage;
    use tempfile::TempDir;

    use super::*;

    struct TestContext {
        _temp_dir: TempDir,
        storage: Box<dyn StorageService>,
    }

    impl TestContext {
        fn new() -> Self {
            let temp_dir = TempDir::new().expect("Failed to create temp dir");
            let db_path = temp_dir.path().to_str().unwrap();

            // Set up database path
            let database_url = format!("{}/test.db", db_path);
            let _ = fs::remove_file(&database_url); // Clean up any existing file

            // Create empty database file
            fs::write(&database_url, "").expect("Failed to create database file");

            // Create connection and run migrations
            let mut conn = SqliteConnection::establish(&database_url)
                .expect("Failed to connect to test database");

            conn.run_pending_migrations(MIGRATIONS)
                .expect("Failed to run migrations");

            // Drop connection before creating storage service
            drop(conn);

            // Create storage service
            let storage =
                Service::storage_service(db_path).expect("Failed to create storage service");

            Self { _temp_dir: temp_dir, storage: Box::new(storage) }
        }
    }

    #[tokio::test]
    async fn test_create_conversation() {
        let ctx = TestContext::new();
        let request = ProviderRequest::new(ModelId::default());

        let conversation = ctx
            .storage
            .create_conversation(&request)
            .await
            .expect("Failed to create conversation");

        assert!(!conversation.id.to_string().is_empty());
    }

    #[tokio::test]
    async fn test_get_request() {
        let ctx = TestContext::new();
        let original_request = ProviderRequest::new(ModelId::default())
            .add_message(CompletionMessage::user("test message"));

        // First create a conversation
        let conversation = ctx
            .storage
            .create_conversation(&original_request)
            .await
            .expect("Failed to create conversation");

        // Then retrieve it
        let retrieved_request = ctx.storage.get_request(conversation.id).await;

        assert_eq!(original_request, retrieved_request);
    }

    #[tokio::test]
    async fn test_get_all_conversation() {
        let ctx = TestContext::new();
        let request1 = ProviderRequest::new(ModelId::default())
            .add_message(CompletionMessage::user("test message"));
        let request2 = ProviderRequest::new(ModelId::default())
            .add_message(CompletionMessage::assistant("test message2", None));

        // Create two conversations
        let _conv1 = ctx
            .storage
            .create_conversation(&request1)
            .await
            .expect("Failed to create first conversation");
        let _conv2 = ctx
            .storage
            .create_conversation(&request2)
            .await
            .expect("Failed to create second conversation");

        // Retrieve all conversations
        let conversations = ctx
            .storage
            .get_all_conversation()
            .await
            .expect("Failed to get all conversations");

        assert_eq!(conversations.len(), 2);
    }

    #[tokio::test]
    async fn test_update_conversation() {
        let ctx = TestContext::new();
        let initial_request = ProviderRequest::new(ModelId::default())
            .add_message(CompletionMessage::system("initial message"));
        let mut updated_request = ProviderRequest::new(ModelId::default());
        updated_request
            .messages
            .push(CompletionMessage::user("test message"));

        // First create a conversation
        let conversation = ctx
            .storage
            .create_conversation(&initial_request)
            .await
            .expect("Failed to create conversation");

        // Update the conversation
        let _ = ctx
            .storage
            .update_conversation(conversation.id, &updated_request)
            .await
            .expect("Failed to update conversation")
            .expect("No conversation found");

        // Verify the update
        let retrieved_request = ctx.storage.get_request(conversation.id).await;
        assert_eq!(updated_request, retrieved_request);
    }

    #[tokio::test]
    async fn test_update_nonexistent_conversation() {
        let ctx = TestContext::new();
        let request = ProviderRequest::new(ModelId::default());

        // Try to update a conversation that doesn't exist
        let result = ctx
            .storage
            .update_conversation(Uuid::new_v4(), &request)
            .await
            .expect("Failed to attempt update");

        assert!(result.is_none());
    }
}
