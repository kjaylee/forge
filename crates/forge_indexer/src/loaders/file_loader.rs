use anyhow::{Context, Result, anyhow};
use forge_walker::Walker;
use std::path::{Path, PathBuf};
use tracing::info;
use tree_sitter::Language;

use super::{FileLoad, Loader};

#[derive(Default)]
pub struct FileLoader {
    exts: Option<Vec<String>>,
}

/// Maps a file extension to its corresponding Tree-sitter language
fn ext_to_language(ext: &str) -> Result<Language> {
    match ext {
        "rs" => Ok(tree_sitter_rust::LANGUAGE.into()),
        _ => Err(anyhow!("Unsupported language: {}", ext)),
    }
}

/// Gets the language for a file path based on its extension
fn path_to_language(path: &Path) -> Result<Language> {
    let ext = path
        .extension()
        .ok_or_else(|| anyhow!("File has no extension: {}", path.display()))?
        .to_str()
        .ok_or_else(|| anyhow!("Non-UTF8 extension in path: {}", path.display()))?;

    ext_to_language(ext)
}

impl FileLoader {
    /// Sets the file extensions to load
    pub fn with_extensions(mut self, exts: Vec<String>) -> Self {
        self.exts = Some(exts);
        self
    }

    /// Loads files from the given path
    async fn load(&self, path: &Path) -> Result<Vec<FileLoad>> {
        if path.is_dir() {
            self.load_directory(path).await
        } else {
            self.load_single_file(path).map(|file| vec![file])
        }
    }

    /// Loads a single file and returns its content and language
    fn load_single_file(&self, path: &Path) -> Result<FileLoad> {
        let content = std::fs::read_to_string(path)
            .with_context(|| format!("Failed to read file: {}", path.display()))?;

        let language = path_to_language(path)
            .with_context(|| format!("Failed to determine language for: {}", path.display()))?;

        Ok(FileLoad { content, path: path.to_path_buf(), language })
    }

    /// Loads files from the given directory
    async fn load_directory(&self, path: &Path) -> Result<Vec<FileLoad>> {
        let walker = Walker::max_all();
        let files = walker
            .cwd(path.to_path_buf())
            .get()
            .await
            .with_context(|| format!("Failed to walk directory: {}", path.display()))?
            .into_iter()
            .filter(|f| self.should_include_file(&PathBuf::from(&f.path)))
            .collect::<Vec<_>>();

        let mut result = Vec::with_capacity(files.len());
        for file in files {
            let file_path = PathBuf::from(&file.path);
            result.push(self.load_file(&file_path)?);
        }

        result.sort();
        Ok(result)
    }

    /// Returns true if the file should be included based on its extension
    fn should_include_file(&self, path: &PathBuf) -> bool {
        self.exts.as_ref().map_or(false, |exts| {
            path.extension().map_or(false, |ext| {
                exts.contains(&ext.to_string_lossy().to_string())
            })
        })
    }

    /// Loads a single file and returns its content and language
    fn load_file(&self, path: &PathBuf) -> Result<FileLoad> {
        let content = std::fs::read_to_string(path)
            .with_context(|| format!("Failed to read file: {}", path.display()))?;

        let language = path_to_language(path)
            .with_context(|| format!("Failed to determine language for: {}", path.display()))?;

        Ok(FileLoad { content, path: path.clone(), language })
    }
}

#[async_trait::async_trait]
impl Loader for FileLoader {
    async fn load(&self, path: &Path) -> Result<Vec<FileLoad>> {
        info!("Loading files from: {}", path.display());
        let result = self.load(path).await;
        info!("Loaded files from: {}", path.display());
        result
    }
}
