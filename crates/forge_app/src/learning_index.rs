use anyhow::Result;
use rusqlite::{ffi::sqlite3_auto_extension, Connection};
use sqlite_vec::sqlite3_vec_init;

#[derive(Clone)]
pub struct IndexConfig {
    pub index_name: String,
    pub vector_size: usize,
    pub column_name: String,
}

pub struct LearningIndex {
    conn: Connection,
    config: IndexConfig,
}

unsafe impl Send for LearningIndex {}

impl LearningIndex {
    pub fn new(path: &str, config: IndexConfig) -> Result<Self> {
        unsafe {
            sqlite3_auto_extension(Some(sqlite3_vec_init));
        }
        let conn = Connection::open(path)?;


        // Create the vector table if it doesn't exist
        let create_table = format!(
            "CREATE VIRTUAL TABLE IF NOT EXISTS {} USING vec0(id TEXT PRIMARY KEY, {} FLOAT[{}])",
            config.index_name, config.column_name, config.vector_size
        );
        conn.execute(&create_table, [])?;

        Ok(Self { conn, config })
    }

    pub fn add(&self, id: String, vector: Vec<f32>) -> Result<()> {
        let insert_sql = format!(
            "INSERT OR REPLACE INTO {}(id, {}) VALUES (?, ?)",
            self.config.index_name, self.config.column_name
        );

        self.conn.execute(&insert_sql, rusqlite::params![id, vec_to_bytes(&vector)])?;
        Ok(())
    }

    pub fn search(&self, query: Vec<f32>, limit: usize) -> Result<Vec<(String, f64)>> {
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

        let results: Vec<(String, f64)> = self.conn
            .prepare(&search_sql)?
            .query_map([vec_to_bytes(&query)], |row| Ok((row.get(0)?, row.get(1)?)))?
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
        let config = IndexConfig {
            index_name: "test_embeddings".to_string(),
            vector_size: 3,
            column_name: "embedding".to_string(),
        };

        let index = LearningIndex::new(":memory:", config.clone())?;

        // Test batch insert
        let test_embeddings = vec![
            ("1".to_string(), vec![0.1, 0.2, 0.3]),    // Document about cats
            ("2".to_string(), vec![0.15, 0.25, 0.35]), // Document about pets
            ("3".to_string(), vec![0.8, 0.9, 1.0]),    // Document about space
        ];

        for (id, embedding) in test_embeddings {
            index.add(id, embedding)?;
        }

        // Test similarity search
        let query = vec![0.12, 0.22, 0.32]; // Query about pets/cats
        let results = index.search(query, 2)?;

        assert_eq!(results.len(), 2);
        // The closest results should be the pet-related documents (ids 1 and 2)
        assert!(results[0].0 == "1" || results[0].0 == "2");
        assert!(results[1].0 == "1" || results[1].0 == "2");
        assert!(results[0].1 <= results[1].1); // Verify distances are ordered
        Ok(())
    }
}
