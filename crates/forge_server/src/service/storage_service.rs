use chrono::{DateTime, NaiveDateTime, Utc};
use derive_setters::Setters;
use diesel::prelude::*;
use diesel::sql_types::{Text, Timestamp, Bool};
use diesel_migrations::{embed_migrations, EmbeddedMigrations};
use forge_provider::{Request as ProviderRequest, Request};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

use crate::schema::conversations;
use crate::Result;
use crate::service::db_pool_service::{DbPoolService, LiveDbPool};

use super::Service;

pub const MIGRATIONS: EmbeddedMigrations = embed_migrations!("migrations");

#[derive(Debug, Setters, Serialize, Deserialize)]
pub struct Conversation {
    pub id: ConversationId,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub meta: Option<ConversationMeta>,
    pub context: Request,
    pub archived: bool,
}

impl Conversation {
    pub fn new(context: Request) -> Self {
        Self {
            id: ConversationId::generate(),
            meta: None,
            context,
            archived: false,
        }
    }
}

#[derive(Debug, Serialize, Deserialize, Clone)]
#[serde(transparent)]
pub struct ConversationId(Uuid);

impl ConversationId {
    pub fn generate() -> Self {
        Self(Uuid::new_v4())
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct ConversationMeta {
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

#[derive(Debug, Insertable, Queryable, QueryableByName)]
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
    #[diesel(sql_type = Bool)]
    archived: bool,
}

impl TryFrom<RawConversation> for Conversation {
    type Error = crate::error::Error;

    fn try_from(raw: RawConversation) -> Result<Self> {
        Ok(Conversation {
            id: ConversationId(Uuid::parse_str(&raw.id).unwrap()),
            meta: Some(ConversationMeta {
                created_at: DateTime::from_naive_utc_and_offset(raw.created_at, Utc),
                updated_at: DateTime::from_naive_utc_and_offset(raw.updated_at, Utc),
            }),
            context: serde_json::from_str(&raw.content)?,
            archived: raw.archived,
        })
    }
}

#[async_trait::async_trait]
pub trait StorageService: Send + Sync {
    async fn set_conversation(&self, request: &ProviderRequest, id: Option<ConversationId>) -> Result<Conversation>;
    async fn get_conversation(&self, id: ConversationId) -> Result<Conversation>;
    async fn list_conversations(&self) -> Result<Vec<Conversation>>;
    async fn archive_conversation(&self, id: ConversationId) -> Result<Conversation>;
}

pub struct Live<P: DbPoolService> {
    pool_service: P,
}

impl<P: DbPoolService> Live<P> {
    pub fn new(pool_service: P) -> Self {
        Self { pool_service }
    }
}

#[async_trait::async_trait]
impl<P: DbPoolService + Send + Sync> StorageService for Live<P> {
    async fn set_conversation(&self, request: &ProviderRequest, id: Option<ConversationId>) -> Result<Conversation> {
        let pool = self.pool_service.get_pool().await?;
        let mut conn = pool.get()?;
        let id = id.unwrap_or_else(ConversationId::generate);

        let raw = RawConversation {
            id: id.0.to_string(),
            created_at: Utc::now().naive_utc(),
            updated_at: Utc::now().naive_utc(),
            content: serde_json::to_string(request)?,
            archived: false,
        };

        diesel::insert_into(conversations::table)
            .values(&raw)
            .on_conflict(conversations::id)
            .do_update()
            .set((
                conversations::content.eq(&raw.content),
                conversations::updated_at.eq(&raw.updated_at),
            ))
            .execute(&mut conn)?;

        let raw: RawConversation = conversations::table
            .find(id.0.to_string())
            .first(&mut conn)?;

        Conversation::try_from(raw)
    }

    async fn get_conversation(&self, id: ConversationId) -> Result<Conversation> {
        let pool = self.pool_service.get_pool().await?;
        let mut conn = pool.get()?;
        let raw: RawConversation = conversations::table
            .find(id.0.to_string())
            .first(&mut conn)?;

        Conversation::try_from(raw)
    }

    async fn list_conversations(&self) -> Result<Vec<Conversation>> {
        let pool = self.pool_service.get_pool().await?;
        let mut conn = pool.get()?;
        let raw: Vec<RawConversation> = conversations::table
            .load(&mut conn)?;

        raw.into_iter().map(Conversation::try_from).collect()
    }

    async fn archive_conversation(&self, id: ConversationId) -> Result<Conversation> {
        let pool = self.pool_service.get_pool().await?;
        let mut conn = pool.get()?;

        diesel::update(conversations::table.find(id.0.to_string()))
            .set(conversations::archived.eq(true))
            .execute(&mut conn)?;

        let raw: RawConversation = conversations::table
            .find(id.0.to_string())
            .first(&mut conn)?;

        Conversation::try_from(raw)
    }
}

impl Service {
    pub fn storage_service(database_url: &str) -> Result<impl StorageService> {
        let pool_service = LiveDbPool::new(database_url, MIGRATIONS)?;
        Ok(Live::new(pool_service))
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use super::super::db_pool_service::tests::TestDbPool;
    use forge_provider::ModelId;
    pub struct TestStorage;
    impl TestStorage {
        pub fn live() -> Result<impl StorageService> {
            let pool_service = TestDbPool::new(MIGRATIONS)?;
            Ok(Live::new(pool_service))
        }
        
    }

    #[tokio::test]
    async fn test_set_and_get_conversation() {
        let ctx = TestStorage::live().expect("Failed to create storage service");
        let request = ProviderRequest::new(ModelId::default());
        let id = ConversationId::generate();

        // Set conversation
        let conversation = ctx
            .set_conversation(&request, Some(id.clone()))
            .await
            .expect("Failed to set conversation");

        assert_eq!(conversation.id.0, id.0);

        // Get conversation
        let retrieved = ctx
            .get_conversation(id.clone())
            .await
            .expect("Failed to get conversation");

        assert_eq!(retrieved.id.0, id.0);
    }

    #[tokio::test]
    async fn test_list_conversations() {
        let ctx = TestStorage::live().expect("Failed to create storage service");
        let request1 = ProviderRequest::new(ModelId::default());
        let request2 = ProviderRequest::new(ModelId::default());
        let id1 = ConversationId::generate();
        let id2 = ConversationId::generate();

        // Create two conversations
        let _conv1 = ctx
            .set_conversation(&request1, Some(id1))
            .await
            .expect("Failed to set first conversation");
        let _conv2 = ctx
            .set_conversation(&request2, Some(id2))
            .await
            .expect("Failed to set second conversation");

        // List all conversations
        let conversations = ctx
            .list_conversations()
            .await
            .expect("Failed to list conversations");

        assert_eq!(conversations.len(), 2);
    }

    #[tokio::test]
    async fn test_archive_conversation() {
        let ctx = TestStorage::live().expect("Failed to create storage service");
        let request = ProviderRequest::new(ModelId::default());
        let id = ConversationId::generate();

        // Create conversation
        let conversation = ctx
            .set_conversation(&request, Some(id.clone()))
            .await
            .expect("Failed to set conversation");

        assert!(!conversation.archived);

        // Archive conversation
        let archived = ctx
            .archive_conversation(id.clone())
            .await
            .expect("Failed to archive conversation");

        assert!(archived.archived);
    }
}
