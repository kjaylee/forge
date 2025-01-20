use std::collections::HashMap;
use std::path::{Path, PathBuf};

use tokenizers::models::bpe::BPE;
use tokenizers::Model;

use crate::error::Error;
use crate::graph::DependencyGraph;
use crate::parser::Parser;
use crate::ranking::{PageRankConfig, SymbolReference};
use crate::symbol::Symbol;

/// A map of a repository's code structure and relationships.
pub struct RepoMap {
    /// Root path used for relative path resolution
    root_path: PathBuf,
    /// Map of file paths to their contained symbols
    files: HashMap<PathBuf, Vec<Symbol>>,
    /// Graph representing relationships between files
    graph: DependencyGraph,
    /// Parser for analyzing source code
    parser: Parser,
    /// Maximum number of tokens to include in context
    token_budget: usize,
}

/// Represents a source file with its content
pub struct SourceFile {
    /// Path to the file, used for symbol resolution
    pub path: PathBuf,
    /// Raw content of the file
    pub content: String,
}

impl RepoMap {
    pub fn new(root_path: PathBuf, token_budget: usize) -> Result<Self, Error> {
        Ok(Self {
            root_path,
            files: HashMap::new(),
            graph: DependencyGraph::new(),
            parser: Parser::new()?,
            token_budget,
        })
    }

    /// Configure PageRank parameters for importance calculation
    pub fn with_page_rank_config(mut self, config: PageRankConfig) -> Self {
        self.graph = self.graph.with_page_rank_config(config);
        self
    }

    /// Process a batch of source files
    pub fn process_files(&mut self, source_files: Vec<SourceFile>) -> Result<(), Error> {
        for source_file in source_files {
            if self.is_supported_file(&source_file.path) {
                self.process_file_content(&source_file.path, &source_file.content)?;
            }
        }

        self.build_dependency_graph();
        Ok(())
    }

    /// Process a single source file
    pub fn process_file(&mut self, source_file: SourceFile) -> Result<(), Error> {
        if self.is_supported_file(&source_file.path) {
            self.process_file_content(&source_file.path, &source_file.content)?;
            self.build_dependency_graph();
        }
        Ok(())
    }

    fn is_supported_file(&self, path: &Path) -> bool {
        path.extension()
            .and_then(|ext| ext.to_str())
            .map(|ext| matches!(ext, "rs" | "js" | "py" | "ts" | "tsx"))
            .unwrap_or(false)
    }

    fn process_file_content(&mut self, path: &Path, content: &str) -> Result<(), Error> {
        let symbols = self.parser.parse_file(path, content)?;
        self.files.insert(path.to_path_buf(), symbols);
        Ok(())
    }

    fn build_dependency_graph(&mut self) {
        // Rebuild the graph from scratch
        self.graph = DependencyGraph::new();

        // Add files and their dependencies to the graph with symbol information
        for (file_path, symbols) in &self.files {
            for symbol in symbols {
                for reference in &symbol.references {
                    let symbol_ref = SymbolReference {
                        name: symbol.name.clone(),
                        kind: symbol.kind.clone(),
                        count: 1, // For now, we count each reference as 1
                    };
                    self.graph
                        .add_symbol_reference(file_path, &reference.path, symbol_ref);
                }
            }
        }
    }

    pub fn get_context(&self, focused_paths: &[PathBuf]) -> anyhow::Result<String> {
        let importance_scores = self.graph.calculate_importance(focused_paths);
        let mut context = String::new();

        // Add focused files first
        for path in focused_paths {
            if let Some(symbols) = self.files.get(path) {
                self.append_file_context(&mut context, path, symbols);
            }
        }

        // Add other important files until we hit the token budget
        let mut other_files: Vec<_> = self
            .files
            .iter()
            .filter(|(path, _)| !focused_paths.contains(path))
            .collect();

        other_files.sort_by(|(path_a, _), (path_b, _)| {
            let score_a = importance_scores.get(*path_a).unwrap_or(&0.0);
            let score_b = importance_scores.get(*path_b).unwrap_or(&0.0);
            score_b.partial_cmp(score_a).unwrap()
        });

        for (path, symbols) in other_files {
            let len = BPE::builder()
                .build()
                .map_err(|e| anyhow::anyhow!(e))?
                .tokenize(&context)
                .map_err(|e| anyhow::anyhow!(e))?
                .len();
            if len >= self.token_budget {
                break;
            }
            self.append_file_context(&mut context, path, symbols);
        }

        Ok(context)
    }

    fn append_file_context(&self, context: &mut String, path: &Path, symbols: &[Symbol]) {
        if !context.is_empty() {
            context.push_str("\n\n");
        }

        if let Ok(rel_path) = path.strip_prefix(&self.root_path) {
            context.push_str(&format!("{}:\n", rel_path.display()));

            // Sort symbols by importance
            let mut symbols = symbols.to_vec();
            symbols.sort_by(|a, b| b.importance.partial_cmp(&a.importance).unwrap());

            for symbol in symbols {
                let signature = symbol.signature.as_deref().unwrap_or(&symbol.name);
                context.push_str(&format!("│{} {}\n", symbol.kind, signature));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{fs, path::PathBuf};

    use super::*;

    #[test]
    fn test_process_single_file() -> Result<(), Error> {
        let root = PathBuf::from("/test");
        let mut repo_map = RepoMap::new(root.clone(), 1000)?;

        let source = SourceFile {
            path: root.join("test.rs"),
            content: r#"
                fn test_function() {
                    println!("Hello");
                }
            "#
            .to_string(),
        };

        repo_map.process_file(source)?;

        // Verify the file was processed
        assert!(repo_map.files.contains_key(&root.join("test.rs")));
        let symbols = repo_map.files.get(&root.join("test.rs")).unwrap();
        assert_eq!(symbols.len(), 1);
        assert_eq!(symbols[0].name.as_str(), "test_function");

        Ok(())
    }

    #[test]
    fn test_process_multiple_files() -> Result<(), Error> {
        let root = PathBuf::from("/test");
        let mut repo_map = RepoMap::new(root.clone(), 1000)?;

        let sources = vec![
            SourceFile {
                path: root.join("file1.rs"),
                content: "fn function1() {}".to_string(),
            },
            SourceFile {
                path: root.join("file2.rs"),
                content: "fn function2() {}".to_string(),
            },
        ];

        repo_map.process_files(sources)?;

        // Verify both files were processed
        assert!(repo_map.files.contains_key(&root.join("file1.rs")));
        assert!(repo_map.files.contains_key(&root.join("file2.rs")));

        Ok(())
    }

    #[test]
    fn test_unsupported_file_type() -> Result<(), Error> {
        let root = PathBuf::from("/test");
        let mut repo_map = RepoMap::new(root.clone(), 1000)?;

        let source = SourceFile {
            path: root.join("test.txt"),
            content: "Some text content".to_string(),
        };

        repo_map.process_file(source)?;

        // Verify the unsupported file was not processed
        assert!(!repo_map.files.contains_key(&root.join("test.txt")));

        Ok(())
    }

    #[tokio::test]
    async fn test_directory_context_snapshot() -> anyhow::Result<()> {
        use insta::assert_snapshot;
        
        let test_root = PathBuf::from("/test/workspace");
        let mut repo_map = RepoMap::new(test_root.clone(), 10000)?;
        
        let src_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src");
        let mut source_files = Vec::new();
        let mut entries = tokio::fs::read_dir(&src_dir).await?;
        
        while let Some(entry) = entries.next_entry().await? {
            let path = entry.path();
            if path.extension()
                .and_then(|ext| ext.to_str())
                .map(|ext| matches!(ext, "rs"))
                .unwrap_or(false) 
            {
                let relative_path = path.strip_prefix(&src_dir).unwrap();
                let test_path = test_root.join("src").join(relative_path);
                let content = tokio::fs::read_to_string(&path).await?;
                source_files.push(SourceFile {
                    path: test_path,
                    content,
                });
            }
        }
            
        source_files.sort_by(|a, b| a.path.cmp(&b.path));
        repo_map.process_files(source_files)?;
        let context = repo_map.get_context(&[])?;
        assert_snapshot!(context);
        
        Ok(())
    }
}