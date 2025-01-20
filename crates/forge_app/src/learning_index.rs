use anyhow::Result;
use derive_setters::Setters;
use rusqlite::{ffi::sqlite3_auto_extension, Connection};
use sqlite_vec::sqlite3_vec_init;

#[derive(Debug)]
pub struct SearchResult {
    pub id: String,
    pub distance: f64,
}

#[derive(Setters)]
#[setters(into)]
pub struct LearningIndexBuilder {
    path: String,
    index_name: String,
    vector_size: usize,
    column_name: String,
}

impl LearningIndexBuilder {
    pub fn new(path: impl Into<String>) -> Self {
        Self {
            path: path.into(),
            index_name: "embeddings".to_string(),
            vector_size: 384,
            column_name: "embedding".to_string(),
        }
    }

    pub fn build(self) -> Result<LearningIndex> {
        LearningIndex::new(self)
    }
}

struct Config {
    index_name: String,
    vector_size: usize,
    column_name: String,
}

pub struct LearningIndex {
    conn: Connection,
    config: Config,
}

unsafe impl Send for LearningIndex {}

impl LearningIndex {
    fn new(builder: LearningIndexBuilder) -> Result<Self> {
        unsafe {
            sqlite3_auto_extension(Some(sqlite3_vec_init));
        }
        let conn = Connection::open(&builder.path)?;

        let config = Config {
            index_name: builder.index_name,
            vector_size: builder.vector_size,
            column_name: builder.column_name,
        };

        // Create the vector table if it doesn't exist
        let create_table = format!(
            "CREATE VIRTUAL TABLE IF NOT EXISTS {} USING vec0(id TEXT PRIMARY KEY, {} FLOAT[{}])",
            config.index_name, config.column_name, config.vector_size
        );
        conn.execute(&create_table, [])?;

        Ok(Self { conn, config })
    }

    pub fn add(&self, id: impl AsRef<str>, vector: &[f32]) -> Result<()> {
        let insert_sql = format!(
            "INSERT OR REPLACE INTO {}(id, {}) VALUES (?, ?)",
            self.config.index_name, self.config.column_name
        );

        self.conn.execute(
            &insert_sql,
            rusqlite::params![id.as_ref(), vec_to_bytes(vector)],
        )?;
        Ok(())
    }

    pub fn search(&self, query: &[f32], limit: usize) -> Result<Vec<SearchResult>> {
        let search_sql = format!(
            r"
            SELECT
                id,
                distance
            FROM {}
            WHERE {} MATCH ?
            ORDER BY distance
            LIMIT {}
            ",
            self.config.index_name, self.config.column_name, limit
        );

        let results = self
            .conn
            .prepare(&search_sql)?
            .query_map([vec_to_bytes(query)], |row| {
                Ok(SearchResult { id: row.get(0)?, distance: row.get(1)? })
            })?
            .collect::<Result<Vec<_>, _>>()?;

        Ok(results)
    }
}

fn vec_to_bytes(v: &[f32]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(v.len() * 4);
    for &x in v {
        bytes.extend_from_slice(&x.to_le_bytes());
    }
    bytes
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vector_operations() -> Result<()> {
        let index = LearningIndexBuilder::new(":memory:")
            .vector_size(3 as usize)
            .index_name("test_embeddings")
            .build()?;

        // Add test vectors
        index.add("1", &[0.1, 0.2, 0.3])?; // Document about cats
        index.add("2", &[0.15, 0.25, 0.35])?; // Document about pets
        index.add("3", &[0.8, 0.9, 1.0])?; // Document about space

        // Test similarity search
        let query = [0.12, 0.22, 0.32]; // Query about pets/cats
        let results = index.search(&query, 2)?;

        println!("{:?}", results);
        assert_eq!(results.len(), 2);
        // The closest results should be the pet-related documents (ids 1 and 2)
        assert!(results[0].id == "1" || results[0].id == "2");
        assert!(results[1].id == "1" || results[1].id == "2");
        assert!(results[0].distance <= results[1].distance); // Verify distances are ordered
        Ok(())
    }
}
