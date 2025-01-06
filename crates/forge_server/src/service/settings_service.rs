use chrono::{DateTime, NaiveDateTime, Utc};
use derive_setters::Setters;
use diesel::prelude::*;
use diesel::sql_types::{Text, Timestamp};
use forge_domain::ModelId;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use uuid::Uuid;

use super::Service;
use crate::schema::settings;
use crate::service::db_service::DBService;
use crate::Result;

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct SettingId(Uuid);

impl SettingId {
    pub fn new(id: &str) -> Self {
        Self(Uuid::parse_str(id).expect("Invalid SettingId"))
    }

    pub fn generate() -> Self {
        Self(Uuid::new_v4())
    }

    pub fn to_string(&self) -> String {
        self.0.to_string()
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CreateSettingRequest {
    project_path: PathBuf,
    chosen_model: ModelId,
}

impl CreateSettingRequest {
    pub fn new(project_path: PathBuf, chosen_model: ModelId) -> Self {
        Self {
            project_path,
            chosen_model,
        }
    }
}

#[derive(Debug, Setters, Serialize, Deserialize, Clone)]
pub struct Setting {
    pub id: SettingId,
    pub project_path: PathBuf,
    pub chosen_model: ModelId,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub meta: Option<SettingsMeta>,
}

impl Setting {
    pub fn new(project_path: PathBuf, model: ModelId) -> Self {
        Self {
            id: SettingId::generate(),
            project_path,
            chosen_model: model,
            meta: None,
        }
    }
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct SettingsMeta {
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

#[derive(Debug, Insertable, Queryable, QueryableByName)]
#[diesel(table_name = settings)]
struct RawSettings {
    #[diesel(sql_type = Text)]
    id: String,
    #[diesel(sql_type = Text)]
    project_path: String,
    #[diesel(sql_type = Text)]
    chosen_model: String,
    #[diesel(sql_type = Timestamp)]
    created_at: NaiveDateTime,
    #[diesel(sql_type = Timestamp)]
    updated_at: NaiveDateTime,
}

impl TryFrom<RawSettings> for Setting {
    type Error = crate::error::Error;

    fn try_from(raw: RawSettings) -> Result<Self> {
        Ok(Setting {
            id: SettingId::new(&raw.id),
            project_path: PathBuf::from(raw.project_path),
            chosen_model: ModelId::new(&raw.chosen_model),
            meta: Some(SettingsMeta {
                created_at: DateTime::from_naive_utc_and_offset(raw.created_at, Utc),
                updated_at: DateTime::from_naive_utc_and_offset(raw.updated_at, Utc),
            }),
        })
    }
}

#[async_trait::async_trait]
pub trait SettingsService: Send + Sync {
    async fn get_setting(&self, setting_id: SettingId) -> Result<Setting>;
    async fn create_setting(&self, create_setting_req: CreateSettingRequest) -> Result<Setting>;
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
impl<P: DBService + Send + Sync> SettingsService for Live<P> {
    async fn get_setting(&self, setting_id: SettingId) -> Result<Setting> {
        let pool = self.pool_service.pool().await?;
        let mut conn = pool.get()?;

        let raw: RawSettings = settings::table
            .find(setting_id.to_string())
            .first(&mut conn)?;

        Ok(raw.try_into()?)
    }

    async fn create_setting(&self, create_setting_req: CreateSettingRequest) -> Result<Setting> {
        let new_settings = Setting::new(
            create_setting_req.project_path,
            create_setting_req.chosen_model,
        );
        let pool = self.pool_service.pool().await?;
        let mut conn = pool.get()?;
        let now = Utc::now().naive_utc();

        let raw = RawSettings {
            id: new_settings.id.to_string(),
            project_path: new_settings.project_path.to_string_lossy().to_string(),
            chosen_model: new_settings.chosen_model.as_str().to_string(),
            created_at: now,
            updated_at: now,
        };

        diesel::insert_into(settings::table)
            .values(&raw)
            .on_conflict(settings::id)
            .do_update()
            .set((
                settings::chosen_model.eq(&raw.chosen_model),
                settings::updated_at.eq(&raw.updated_at),
            ))
            .execute(&mut conn)?;

        let raw: RawSettings = settings::table.find(raw.id).first(&mut conn)?;
        Ok(raw.try_into()?)
    }
}

impl Service {
    pub fn settings_service(database_url: &str) -> Result<impl SettingsService> {
        Ok(Live::new(Service::db_pool_service(database_url)?))
    }
}

#[cfg(test)]
pub mod tests {
    use super::super::db_service::tests::TestDbPool;
    use super::*;

    pub struct TestStorage;

    impl TestStorage {
        pub fn in_memory() -> Result<impl SettingsService> {
            let pool_service = TestDbPool::new()?;
            Ok(Live::new(pool_service))
        }
    }

    async fn setup_storage() -> Result<impl SettingsService> {
        TestStorage::in_memory()
    }

    #[tokio::test]
    async fn test_settings_can_be_stored_and_retrieved() -> Result<()> {
        let storage = setup_storage().await?;
        let project_path = PathBuf::from("/test/project");
        let settings = CreateSettingRequest::new(project_path.clone(), ModelId::new("gpt-4"));

        let stored = storage.create_setting(settings.clone()).await?;
        assert_eq!(stored.chosen_model, settings.chosen_model);
        assert_eq!(stored.project_path, settings.project_path);
        assert!(stored.meta.is_some());

        let retrieved = storage.get_setting(stored.id).await?;
        assert_eq!(retrieved.chosen_model, settings.chosen_model);
        Ok(())
    }
}
