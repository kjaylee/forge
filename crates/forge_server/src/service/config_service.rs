use std::fmt::Display;

use chrono::{DateTime, NaiveDateTime, Utc};
use derive_more::derive::Display;
use derive_setters::Setters;
use diesel::prelude::*;
use diesel::sql_types::{Nullable, Text, Timestamp};
use forge_domain::ModelId;
use serde::{Deserialize, Serialize};

use super::Service;
use crate::error::Result;
use crate::schema::configurations;
use crate::service::db_service::DBService;

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
enum ProviderType {
    #[serde(alias = "primary")]
    Primary,
    #[serde(alias = "secondary")]
    Secondary,
}

impl Display for ProviderType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProviderType::Primary => write!(f, "primary"),
            ProviderType::Secondary => write!(f, "secondary"),
        }
    }
}

#[derive(Debug, Display)]
pub enum ConfigError {
    Invalid(String),
}

impl TryFrom<String> for ProviderType {
    type Error = crate::error::Error;

    fn try_from(provider_type_str: String) -> Result<Self> {
        match provider_type_str.to_lowercase().as_str() {
            "primary" => Ok(ProviderType::Primary),
            "secondary" => Ok(ProviderType::Secondary),
            _ => Err(ConfigError::Invalid(format!(
                "Invalid provider type '{}'. Expected one of: 'primary', 'secondary'",
                provider_type_str
            ))
            .into()),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CreateConfigRequest {
    provider_type: ProviderType,
    provider_id: String,
    model_id: ModelId,
    api_key: String,
}

#[derive(Debug, Setters, Serialize, Deserialize, Clone)]
pub struct Config {
    provider_type: ProviderType,
    provider_id: String,
    model_id: ModelId,
    api_key: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub meta: Option<ConfigMeta>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct GlobalConfig(Vec<Config>);

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct ConfigMeta {
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

#[derive(Debug, Insertable, Queryable, QueryableByName)]
#[diesel(table_name = configurations)]
struct RawConfig {
    #[diesel(sql_type = Text)]
    provider_type: String,
    #[diesel(sql_type = Text)]
    provider_id: String,
    #[diesel(sql_type = Text)]
    model_id: String,
    #[diesel(sql_type = Nullable<Text>)]
    api_key: Option<String>,
    #[diesel(sql_type = Timestamp)]
    created_at: NaiveDateTime,
    #[diesel(sql_type = Timestamp)]
    updated_at: NaiveDateTime,
}

impl TryFrom<RawConfig> for Config {
    type Error = crate::error::Error;

    fn try_from(raw: RawConfig) -> Result<Self> {
        Ok(Config {
            provider_type: ProviderType::try_from(raw.provider_type)?,
            provider_id: raw.provider_id,
            model_id: ModelId::new(&raw.model_id),
            api_key: raw.api_key.unwrap_or_default(),
            meta: Some(ConfigMeta {
                created_at: DateTime::from_naive_utc_and_offset(raw.created_at, Utc),
                updated_at: DateTime::from_naive_utc_and_offset(raw.updated_at, Utc),
            }),
        })
    }
}

#[async_trait::async_trait]
pub trait ConfigService: Send + Sync {
    async fn get(&self) -> Result<GlobalConfig>;
    async fn set(&self, config: CreateConfigRequest) -> Result<Config>;
}

pub struct Live<P> {
    pool_service: P,
}

impl<P: DBService> Live<P> {
    pub fn new(pool_service: P) -> Self {
        Self { pool_service }
    }
}

#[async_trait::async_trait]
impl<P: DBService + Send + Sync> ConfigService for Live<P> {
    async fn get(&self) -> Result<GlobalConfig> {
        let pool = self.pool_service.pool().await?;
        let mut conn = pool.get()?;

        let mut configs = Vec::with_capacity(2);

        // Try to get primary config if it exists
        if let Ok(primary_raw) = configurations::table
            .filter(configurations::provider_type.eq("primary"))
            .first::<RawConfig>(&mut conn)
        {
            configs.push(primary_raw.try_into()?);
        }

        // Try to get secondary config if it exists
        if let Ok(secondary_raw) = configurations::table
            .filter(configurations::provider_type.eq("secondary"))
            .first::<RawConfig>(&mut conn)
        {
            configs.push(secondary_raw.try_into()?);
        }

        Ok(GlobalConfig(configs))
    }

    async fn set(&self, config: CreateConfigRequest) -> Result<Config> {
        let pool = self.pool_service.pool().await?;
        let mut conn = pool.get()?;
        let now = Utc::now().naive_utc();

        let raw = RawConfig {
            provider_type: config.provider_type.to_string(),
            provider_id: config.provider_id,
            model_id: config.model_id.as_str().to_string(),
            api_key: Some(config.api_key),
            created_at: now,
            updated_at: now,
        };

        diesel::insert_into(configurations::table)
            .values(&raw)
            .on_conflict(configurations::provider_type)
            .do_update()
            .set((
                configurations::provider_id.eq(&raw.provider_id),
                configurations::model_id.eq(&raw.model_id),
                configurations::api_key.eq(&raw.api_key),
                configurations::updated_at.eq(&raw.updated_at),
            ))
            .execute(&mut conn)?;

        let raw: RawConfig = configurations::table
            .find(configurations::provider_type)
            .first(&mut conn)?;
        Ok(raw.try_into()?)
    }
}

impl Service {
    pub fn config_service(database_url: &str) -> Result<impl ConfigService> {
        Ok(Live::new(Service::db_pool_service(database_url)?))
    }
}

#[cfg(test)]
pub mod tests {
    use super::super::db_service::tests::TestDbPool;
    use super::*;

    pub struct TestStorage;

    impl TestStorage {
        pub fn in_memory() -> Result<impl ConfigService> {
            let pool_service = TestDbPool::new()?;
            Ok(Live::new(pool_service))
        }
    }

    async fn setup_storage() -> Result<impl ConfigService> {
        TestStorage::in_memory()
    }

    #[tokio::test]
    async fn test_config_can_be_stored_and_retrieved() -> Result<()> {
        let storage = setup_storage().await?;

        // Create primary config
        let primary_config = CreateConfigRequest {
            provider_type: "primary".to_string().try_into().unwrap(),
            provider_id: "openai".to_string(),
            model_id: ModelId::new("gpt-4"),
            api_key: "test-key-1".to_string(),
        };
        let _ = storage.set(primary_config).await?;

        // Create secondary config
        let secondary_config = CreateConfigRequest {
            provider_type: "secondary".to_string().try_into().unwrap(),
            provider_id: "anthropic".to_string(),
            model_id: ModelId::new("claude-2"),
            api_key: "test-key-2".to_string(),
        };
        let _ = storage.set(secondary_config).await?;

        // Retrieve both configs
        let GlobalConfig(configs) = storage.get().await?;
        assert_eq!(configs.len(), 2);

        // Verify primary config
        let primary = configs
            .iter()
            .find(|c| matches!(c.provider_type, ProviderType::Primary))
            .unwrap();
        assert_eq!(primary.provider_id, "openai");
        assert_eq!(primary.model_id.as_str(), "gpt-4");

        // Verify secondary config
        let secondary = configs
            .iter()
            .find(|c| matches!(c.provider_type, ProviderType::Secondary))
            .unwrap();
        assert_eq!(secondary.provider_id, "anthropic");
        assert_eq!(secondary.model_id.as_str(), "claude-2");

        Ok(())
    }
}
