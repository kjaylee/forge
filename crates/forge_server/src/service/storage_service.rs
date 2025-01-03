use diesel::prelude::*;
use diesel::r2d2::{ConnectionManager, Pool};
use diesel::sqlite::SqliteConnection;
use diesel::sql_types::{Text, Timestamp};
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc, NaiveDateTime};
use uuid::Uuid;

use super::Service;
use crate::Result;
use crate::schema::conversations;
use forge_provider::{Request as ProviderRequest, ModelId};

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
        serde_json::from_str(&conv.content)
            .map_err(|e| crate::error::Error::Custom(format!("Failed to deserialize request: {}", e)))
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
            content: serde_json::to_string(request)
                .map_err(|e| crate::error::Error::Custom(format!("Failed to serialize request: {}", e)))?,
        })
    }
}

#[async_trait::async_trait]
pub trait StorageService: Send + Sync {
    async fn create_conversation(&self, request: &ProviderRequest) -> Result<Conversation>;
    async fn get_request(&self, id: Uuid) -> ProviderRequest;
    async fn get_all_requests(&self) -> Result<Vec<ProviderRequest>>;
    async fn update_conversation(&self, id: Uuid, request: &ProviderRequest) -> Result<Option<Conversation>>;
}

struct Live {
    pool: DbPool,
}

impl Live {
    pub fn new(cwd: &str) -> Result<Self> {
        let db_path = format!("{}/conversations.db", cwd);
        let manager = ConnectionManager::<SqliteConnection>::new(db_path);
        let pool = Pool::builder()
            .build(manager)
            .map_err(|e| crate::error::Error::Custom(e.to_string()))?;
        
        Ok(Self { pool })
    }

    // Private implementation method
    async fn get_conversation_impl(&self, conversation_id: Uuid) -> Result<Option<Conversation>> {
        let conn = &mut self.pool.get()
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
        let conn = &mut self.pool.get()
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
            conversation.try_into().unwrap_or_else(|_| ProviderRequest::new(ModelId::default()))
        } else {
            ProviderRequest::new(ModelId::default())
        }
    }

    async fn get_all_requests(&self) -> Result<Vec<ProviderRequest>> {
        let conn = &mut self.pool.get()
            .map_err(|e| crate::error::Error::Custom(e.to_string()))?;
        
        let raw_convs: Vec<RawConversation> = diesel::sql_query("SELECT * FROM conversations")
            .load(conn)
            .map_err(|e| crate::error::Error::Custom(e.to_string()))?;
        
        let convs: Vec<Conversation> = raw_convs.into_iter().map(Into::into).collect();

        convs.into_iter()
            .map(|conv| conv.try_into())
            .collect::<std::result::Result<Vec<_>, _>>()
            .map_err(|e| crate::error::Error::Custom(format!("Failed to deserialize requests: {}", e)))
    }

    async fn update_conversation(&self, conversation_id: Uuid, request: &ProviderRequest) -> Result<Option<Conversation>> {
        use crate::schema::conversations::dsl::*;
        
        let conn = &mut self.pool.get()
            .map_err(|e| crate::error::Error::Custom(e.to_string()))?;

        let content_str = serde_json::to_string(request)
            .map_err(|e| crate::error::Error::Custom(format!("Failed to serialize request: {}", e)))?;

        let updated = diesel::update(conversations.find(conversation_id.to_string()))
            .set(content.eq(content_str))
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
