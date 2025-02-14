use crate::conn::ForgeConnection;
use chrono::{DateTime, NaiveDateTime};
use diesel::prelude::*;
use forge_app::InformationRepository;
use forge_domain::{self as domain};

pub struct ForgeKnowledgeRepository {
    conn: ForgeConnection,
}

impl ForgeKnowledgeRepository {
    pub fn new(conn: ForgeConnection) -> Self {
        Self { conn }
    }
}

#[derive(Queryable, Selectable)]
#[diesel(table_name = crate::schema::knowledge)]
#[diesel(check_for_backend(diesel::sqlite::Sqlite))]
struct Knowledge {
    id: i32,
    content: String,
    encoding: String,
    created_at: NaiveDateTime,
    updated_at: NaiveDateTime,
}

#[derive(Insertable)]
#[diesel(table_name = crate::schema::knowledge)]
#[diesel(check_for_backend(diesel::sqlite::Sqlite))]
struct CreateKnowledge {
    content: String,
    encoding: String,
    created_at: NaiveDateTime,
    updated_at: NaiveDateTime,
}

#[async_trait::async_trait]
impl InformationRepository for ForgeKnowledgeRepository {
    async fn insert(&self, content: &str, encoding: &[f32]) -> anyhow::Result<()> {
        let now = chrono::Utc::now();
        let kb = CreateKnowledge {
            content: content.to_string(),
            encoding: serde_json::to_string(encoding)?,
            created_at: now.naive_utc(),
            updated_at: now.naive_utc(),
        };

        let mut conn = self.conn.init().await?;

        kb.insert_into(crate::schema::knowledge::table)
            .execute(&mut conn)?;

        Ok(())
    }

    async fn search(&self, embed: Vec<f32>) -> anyhow::Result<Vec<domain::Knowledge>> {
        todo!()
    }

    async fn list(&self) -> anyhow::Result<Vec<domain::Knowledge>> {
        let mut conn = self.conn.init().await?;
        let output = crate::schema::knowledge::table
            .load::<Knowledge>(&mut conn)?
            .into_iter()
            .map(|result| result.try_into())
            .collect::<Result<Vec<_>, _>>()?;

        Ok(output)
    }
}

impl TryFrom<Knowledge> for domain::Knowledge {
    type Error = serde_json::Error;
    fn try_from(kb: Knowledge) -> Result<Self, Self::Error> {
        Ok(domain::Knowledge {
            id: domain::KnowledgeId::new(kb.id as u64),
            content: kb.content,
            embedding: serde_json::from_str(&kb.encoding)?,
            created_at: DateTime::from_naive_utc_and_offset(kb.created_at, chrono::Utc),
            updated_at: DateTime::from_naive_utc_and_offset(kb.updated_at, chrono::Utc),
        })
    }
}
