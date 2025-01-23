use super::errors::{FileError, Result};
use forge_walker::Walker;
use std::collections::HashMap;
use std::path::Path;
use tokio::fs;

pub struct GitWalker {}

impl GitWalker {
    pub async fn read_files(&self, root: &Path) -> Result<HashMap<String, Vec<u8>>> {
        let mut files = HashMap::new();
        let walker = Walker::new(root.to_path_buf()).with_max_depth(100);
        
        let entries = walker.get().await
            .map_err(|e| FileError::Git(e.to_string()))?;

        let p = entries.iter().filter(|e| !e.is_dir);

        for entry in p {
            
            
            // Read file content
            let content = fs::read(root.join(&entry.path))
                .await
                .map_err(FileError::Io)?;

            files.insert(entry.path.clone(), content);
        }

        Ok(files)
    }
}