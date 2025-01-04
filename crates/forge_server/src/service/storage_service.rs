use chrono::{DateTime, NaiveDateTime, Utc};
use derive_setters::Setters;
use diesel::prelude::*;
use diesel::sql_types::{Bool, Text, Timestamp};
use diesel_migrations::{embed_migrations, EmbeddedMigrations};
use forge_provider::{Request as ProviderRequest, Request};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

use super::Service;
use crate::schema::conversations;
use crate::service::db_pool_service::{DbPoolService, LiveDbPool};
use crate::Result;

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

#[derive(Debug, Serialize, Deserialize, Clone, PartialEq, Eq, Copy)]
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
    async fn set_conversation(
        &self,
        request: &ProviderRequest,
        id: Option<ConversationId>,
    ) -> Result<Conversation>;
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
    async fn set_conversation(
        &self,
        request: &ProviderRequest,
        id: Option<ConversationId>,
    ) -> Result<Conversation> {
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
        let raw: Vec<RawConversation> = conversations::table.load(&mut conn)?;

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
    use forge_provider::ModelId;

    use super::super::db_pool_service::tests::TestDbPool;
    use super::*;
    pub struct TestStorage;
    impl TestStorage {
        pub fn in_memory() -> Result<impl StorageService> {
            let pool_service = TestDbPool::new(MIGRATIONS)?;
            Ok(Live::new(pool_service))
        }
    }

    async fn setup_storage() -> Result<impl StorageService> {
        TestStorage::in_memory()
    }

    async fn create_conversation(storage: &impl StorageService, id: Option<ConversationId>) -> Result<Conversation> {
        let request = ProviderRequest::new(ModelId::default());
        storage.set_conversation(&request, id).await
    }

    #[tokio::test]
    async fn conversation_can_be_stored_and_retrieved() {
        let storage = setup_storage().await.expect("storage setup failed");
        let id = ConversationId::generate();
        
        let saved = create_conversation(&storage, Some(id.clone()))
            .await
            .expect("failed to create conversation");
        let retrieved = storage
            .get_conversation(id)
            .await
            .expect("failed to retrieve conversation");

        assert_eq!(saved.id.0, retrieved.id.0);
        assert_eq!(saved.context, retrieved.context);
    }

    #[tokio::test]
    async fn list_returns_all_conversations() {
        let storage = setup_storage().await.expect("storage setup failed");
        
        create_conversation(&storage, None).await.expect("failed to create first conversation");
        create_conversation(&storage, None).await.expect("failed to create second conversation");

        let conversations = storage
            .list_conversations()
            .await
            .expect("failed to list conversations");

        assert_eq!(conversations.len(), 2);
        assert!(!conversations[0].archived);
        assert!(!conversations[1].archived);
    }

    #[tokio::test]
    async fn archive_marks_conversation_as_archived() {
        let storage = setup_storage().await.expect("storage setup failed");
        let conversation = create_conversation(&storage, None)
            .await
            .expect("failed to create conversation");

        let archived = storage
            .archive_conversation(conversation.id)
            .await
            .expect("failed to archive conversation");

        assert!(archived.archived);
        assert_eq!(archived.id, conversation.id);
    }
}
