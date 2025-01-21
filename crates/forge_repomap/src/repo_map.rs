use std::collections::HashMap;
use std::path::{Path, PathBuf};

use tokenizers::models::bpe::BPE;
use tokenizers::Model;

use crate::error::Error;
use crate::graph::DependencyGraph;
use crate::parser::Parser;
use crate::ranking::{PageRankConfig, SymbolReference};
use crate::symbol::{Symbol, SymbolKind};

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
        // Rebuild the graph from scratch with default PageRank config
        self.graph = DependencyGraph::new().with_page_rank_config(PageRankConfig::default());

        // Track which file defines each symbol
        let mut definitions: HashMap<String, (PathBuf, SymbolKind)> = HashMap::new();

        // First pass: collect all definitions (no references)
        let mut file_paths: Vec<_> = self.files.keys().cloned().collect();
        // Sort paths for deterministic order
        file_paths.sort();

        // Process files in sorted order for deterministic output
        for file_path in &file_paths {
            // Sort symbols by name for deterministic order
            if let Some(symbols) = self.files.get(file_path) {
                let mut symbols: Vec<_> = symbols.iter().collect();
                symbols.sort_by(|a, b| a.name.cmp(&b.name));

                // Collect definitions (no references)
                for symbol in symbols {
                    if symbol.references.is_empty() {
                        definitions.insert(
                            symbol.name.to_string(),
                            (file_path.clone(), symbol.kind.clone()),
                        );
                    }
                }
            }
        }

        // Second pass: process references in sorted order
        for file_path in &file_paths {
            if let Some(symbols) = self.files.get(file_path) {
                // Sort symbols by name for deterministic order
                let mut symbols: Vec<_> = symbols.iter().collect();
                symbols.sort_by(|a, b| a.name.cmp(&b.name));

                // Process symbols with references
                for symbol in symbols {
                    // Skip symbols without references
                    if !symbol.references.is_empty() {
                        // Check if this symbol is defined elsewhere
                        if let Some((def_file, def_kind)) =
                            definitions.get(&symbol.name.to_string())
                        {
                            // Add edge from source file to definition file
                            let symbol_ref = SymbolReference {
                                name: symbol.name.clone(),
                                kind: def_kind.clone(),
                                count: symbol.references.len(),
                            };

                            // Only add cross-file reference if files are different
                            if file_path.as_path() != def_file.as_path() {
                                self.graph
                                    .add_symbol_reference(file_path, def_file, symbol_ref);
                            }
                        }
                    }
                }
            }
        }
    }

    pub fn get_context(&self, focused_paths: &[PathBuf]) -> anyhow::Result<String> {
        let importance_scores = self.graph.calculate_importance(focused_paths);
        let mut context = String::new();

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

        // Sort by importance first, then maintain path order for stability
        other_files.sort_by(|(path_a, _), (path_b, _)| {
            let score_a = importance_scores.get(path_a.as_path()).unwrap_or(&0.0);
            let score_b = importance_scores.get(path_b.as_path()).unwrap_or(&0.0);

            // First compare scores in reverse order (higher first)
            score_b
                .partial_cmp(score_a)
                .unwrap()
                // If scores are equal, path comparison is implicit due to prior sort
                .then_with(|| path_a.cmp(path_b))
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
            // Use deterministic path string
            let display_path = rel_path.display().to_string().replace('\\', "/");
            context.push_str(&format!("{}:\n", display_path));

            // Sort symbols by kind, then name for complete determinism
            let mut symbols = symbols.to_vec();
            symbols.sort_by(|a, b| {
                // First sort by kind (in consistent order)
                let kind_a = match a.kind {
                    SymbolKind::Module => 1,
                    SymbolKind::Trait => 2,
                    SymbolKind::Struct => 3,
                    SymbolKind::Implementation => 4,
                    SymbolKind::Function | SymbolKind::Method => 5,
                    _ => 6,
                };
                let kind_b = match b.kind {
                    SymbolKind::Module => 1,
                    SymbolKind::Trait => 2,
                    SymbolKind::Struct => 3,
                    SymbolKind::Implementation => 4,
                    SymbolKind::Function | SymbolKind::Method => 5,
                    _ => 6,
                };

                kind_a.cmp(&kind_b).then_with(|| a.name.cmp(&b.name))
            });

            // Output in deterministic order
            for symbol in &symbols {
                let signature = symbol.signature.as_deref().unwrap_or(&symbol.name);
                context.push_str(&format!("│{} {}\n", symbol.kind, signature));
            }
        }
    }
}

#[cfg(test)]
mod tests {
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

        // Should find one function definition
        let function_symbols: Vec<_> = symbols
            .iter()
            .filter(|s| s.references.is_empty()) // Definitions have no references
            .collect();
        assert_eq!(
            function_symbols.len(),
            1,
            "Should have one function definition"
        );
        assert_eq!(function_symbols[0].name.as_str(), "test_function");

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
    fn test_cross_file_references() -> Result<(), Error> {
        let root = PathBuf::from("/test");
        let mut repo_map = RepoMap::new(root.clone(), 1000)?;

        // Create two files with cross-references
        let sources = vec![
            SourceFile {
                path: root.join("lib.rs"),
                content: r#"
                    pub fn helper_function() {
                        // Some implementation
                    }
                "#
                .to_string(),
            },
            SourceFile {
                path: root.join("main.rs"),
                content: r#"
                    fn main() {
                        helper_function(); // First call
                        helper_function(); // Second call
                    }
                "#
                .to_string(),
            },
        ];

        repo_map.process_files(sources)?;

        // Get importance scores
        let scores = repo_map.graph.calculate_importance(&[]);

        // lib.rs should have higher score as it's referenced
        let lib_score = scores.get(&root.join("lib.rs")).unwrap_or(&0.0);
        let main_score = scores.get(&root.join("main.rs")).unwrap_or(&0.0);

        assert!(
            lib_score > &0.0,
            "lib.rs should have a non-zero score (got {})",
            lib_score
        );
        assert!(
            lib_score > main_score,
            "lib.rs ({}) should have higher score than main.rs ({}) as it's referenced",
            lib_score,
            main_score
        );

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
        use std::collections::BTreeMap;

        use insta::assert_snapshot;

        // Set up deterministic test environment
        let test_root = PathBuf::from("/test/workspace");
        let mut repo_map = RepoMap::new(test_root.clone(), 10000)?;

        // Fixed config for deterministic weights
        repo_map = repo_map.with_page_rank_config(PageRankConfig {
            damping_factor: 0.85,
            max_iterations: 100,
            tolerance: 1e-6,
        });

        let src_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src");
        let mut file_map = BTreeMap::new(); // Use BTreeMap for deterministic ordering
        let mut entries = tokio::fs::read_dir(&src_dir).await?;

        // First collect all files in a sorted data structure
        while let Some(entry) = entries.next_entry().await? {
            let path = entry.path();
            if path
                .extension()
                .and_then(|ext| ext.to_str())
                .map(|ext| matches!(ext, "rs"))
                .unwrap_or(false)
            {
                let relative_path = path.strip_prefix(&src_dir).unwrap();
                let test_path = test_root.join("src").join(relative_path);
                let content = tokio::fs::read_to_string(&path).await?;

                // Use canonical path string as key for deterministic ordering
                let key = test_path.to_string_lossy().to_string();
                file_map.insert(key, (test_path, content.replace("\r\n", "\n")));
            }
        }

        // Convert sorted map to vec
        let source_files: Vec<_> = file_map
            .values()
            .map(|(path, content)| SourceFile { path: path.clone(), content: content.clone() })
            .collect();

        repo_map.process_files(source_files)?;

        // Get importance scores
        let scores = repo_map.graph.calculate_importance(&[]);

        // Verify scores (important for determinism)
        assert!(
            scores[&test_root.join("src/ranking.rs")] > 0.0,
            "ranking.rs should have positive weight"
        );
        assert!(
            scores[&test_root.join("src/graph.rs")] > 0.0,
            "graph.rs should have positive weight"
        );

        // Get context with deterministic scores
        let context = repo_map.get_context(&[])?;
        assert_snapshot!(context);

        Ok(())
    }
}
