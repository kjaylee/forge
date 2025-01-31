//! RepoMap module responsible for managing the repository context and analysis.

use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

use anyhow::Result;

use crate::graph::DependencyGraph;
use crate::symbol::{Symbol, SymbolKind};
use crate::{ParseConfig, Parser};

#[derive(Debug, Clone)]
pub struct RepoMapConfig {
    pub max_file_size: usize,
    pub max_files: usize,
    pub parallel_processing: bool,
    pub scope_analysis: bool,
    pub token_budget: usize,
    pub parse_config: ParseConfig,
}

impl Default for RepoMapConfig {
    fn default() -> Self {
        Self {
            max_file_size: 1_000_000, // 1MB
            max_files: 1000,
            parallel_processing: true,
            scope_analysis: true,
            token_budget: 4000, // Default token budget for context generation
            parse_config: ParseConfig::new()
                .with_scope_analysis(true)
                .with_signature_parsing(true)
                .with_reference_tracking(true),
        }
    }
}

// Track where each symbol is defined
#[derive(Debug, Clone)]
#[allow(dead_code)]
struct SymbolDefinition {
    file: PathBuf,
    name: String,
    kind: crate::symbol::SymbolKind,
}

pub struct RepoMap {
    #[allow(dead_code)]
    root_path: PathBuf,
    files: HashMap<PathBuf, Vec<Symbol>>,
    symbol_definitions: HashMap<String, SymbolDefinition>, // Track where each symbol is defined
    graph: DependencyGraph,
    parser: Parser,
    config: RepoMapConfig,
}

impl RepoMap {
    pub fn new(root_path: PathBuf) -> Result<Self> {
        let config = RepoMapConfig::default();
        Ok(Self {
            root_path,
            files: HashMap::new(),
            symbol_definitions: HashMap::new(),
            graph: DependencyGraph::new(),
            parser: Parser::new()?.with_config(config.parse_config.clone()),
            config,
        })
    }

    pub fn with_config(mut self, config: RepoMapConfig) -> Self {
        self.config = config.clone();
        self.parser = self.parser.with_config(config.parse_config);
        self
    }

    pub async fn process_files(&mut self, source_files: Vec<(PathBuf, String)>) -> Result<()> {
        // First pass: collect all defined symbols
        println!("\nFirst pass - collecting symbol definitions:"); // Debug
        for (path, content) in &source_files {
            if !self.is_supported_file(path) {
                continue;
            }

            let symbols = self.parser.parse_file(path, content)?;
            println!("Found {} symbols in {:?}", symbols.len(), path); // Debug

            // Track symbol definitions
            for symbol in &symbols {
                println!("  Defined symbol: {} ({:?})", symbol.name, symbol.kind); // Debug
                if symbol.is_public() {
                    // Only track public symbols
                    self.symbol_definitions.insert(
                        symbol.name.clone(),
                        SymbolDefinition {
                            file: path.clone(),
                            name: symbol.name.clone(),
                            kind: symbol.kind.clone(),
                        },
                    );
                }
            }

            self.files.insert(path.clone(), symbols);
        }

        // Second pass: process references and build the graph
        println!("\nSecond pass - processing references:"); // Debug
        self.build_dependency_graph();

        Ok(())
    }

    fn is_supported_file(&self, path: &std::path::Path) -> bool {
        path.extension()
            .and_then(|ext| ext.to_str())
            .map(|ext| matches!(ext, "rs" | "js" | "py"))
            .unwrap_or(false)
    }

    fn build_dependency_graph(&mut self) {
        // Track which edges we've already added
        let mut added_edges: HashSet<(PathBuf, PathBuf)> = HashSet::new();

        // First, process all files to build the complete graph
        for (file_path, symbols) in &self.files {
            println!("Processing symbols from {:?}", file_path); // Debug

            // Add cross-file references
            for symbol in symbols {
                println!(
                    "  Processing symbol {} with {} references",
                    symbol.name,
                    symbol.references.len()
                ); // Debug

                // Process references to other files
                for reference in &symbol.references {
                    let ref_path = &reference.location.path;
                    let from_path = file_path;
                    let to_path = ref_path.as_ref();

                    // Only add new edges
                    let edge = (from_path.clone(), to_path.clone());
                    if !added_edges.contains(&edge) {
                        // Add edge with appropriate weight
                        let edge_type = match symbol.kind {
                            SymbolKind::Function | SymbolKind::Method => {
                                crate::ranking::EdgeType::Call
                            }
                            SymbolKind::Struct | SymbolKind::Class => {
                                crate::ranking::EdgeType::Implementation
                            }
                            SymbolKind::Module => crate::ranking::EdgeType::Import,
                            _ => crate::ranking::EdgeType::Use,
                        };

                        println!(
                            "    Adding reference: {} -> {} ({:?})",
                            from_path.display(),
                            to_path.display(),
                            edge_type
                        );

                        self.graph
                            .add_symbol_reference(from_path, to_path, edge_type);
                        added_edges.insert(edge);
                    }
                }
            }
        }

        println!("\nFinal graph state:"); // Debug
        self.graph.debug_print_state();
    }

    pub fn get_context(&self, focused_paths: &[PathBuf]) -> Result<String> {
        let importance_scores = self.graph.calculate_importance(focused_paths);
        println!("\nImportance scores:"); // Debug
        for (path, score) in &importance_scores {
            println!("{:?}: {}", path, score); // Debug
        }

        let mut result = String::new();
        let mut token_count = 0;
        let token_budget = self.config.token_budget;

        // Helper function to estimate tokens in a line
        let estimate_tokens = |line: &str| -> usize {
            line.split_whitespace().count() + 2 // +2 for newline and formatting
        };

        // Add content while respecting token budget
        let mut add_content = |path: &PathBuf, symbols: &Vec<Symbol>| -> bool {
            let file_header = format!("\nFile: {}\n", path.display());
            let header_tokens = estimate_tokens(&file_header);

            if token_count + header_tokens > token_budget {
                return false;
            }

            result.push_str(&file_header);
            token_count += header_tokens;

            for symbol in symbols {
                let line = format!("  {} {}\n", symbol.kind, symbol.name);
                let line_tokens = estimate_tokens(&line);

                if token_count + line_tokens > token_budget {
                    result.push_str("  ...\n");
                    return false;
                }

                result.push_str(&line);
                token_count += line_tokens;
            }
            true
        };

        // First add focused files
        for path in focused_paths {
            if let Some(symbols) = self.files.get(path) {
                if !add_content(path, symbols) {
                    break;
                }
            }
        }

        // Then add other important files if budget allows
        let mut files: Vec<(&PathBuf, &Vec<Symbol>)> = self
            .files
            .iter()
            .filter(|(path, _)| !focused_paths.contains(path))
            .collect();

        files.sort_by(|(path_a, _), (path_b, _)| {
            let score_a = importance_scores.get(*path_a).unwrap_or(&0.0);
            let score_b = importance_scores.get(*path_b).unwrap_or(&0.0);
            score_b
                .partial_cmp(score_a)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        for (path, symbols) in files {
            if !add_content(path, symbols) {
                break;
            }
        }

        if token_count >= token_budget {
            result.push_str("\n(Context truncated due to token budget)\n");
        }

        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use insta::assert_snapshot;

    use super::*;

    #[tokio::test]
    async fn test_process_single_file() -> Result<()> {
        let mut repo_map = RepoMap::new(PathBuf::from("test"))?;
        let content = r#"
            pub fn test_function() {
                println!("test");
            }
        "#
        .to_string();

        repo_map
            .process_files(vec![(PathBuf::from("test.rs"), content)])
            .await?;

        let files = &repo_map.files;
        assert_eq!(files.len(), 1);
        assert!(files.contains_key(&PathBuf::from("test.rs")));

        Ok(())
    }

    #[test]
    fn test_supported_files() -> Result<()> {
        let repo_map = RepoMap::new(PathBuf::from("test"))?;

        assert!(repo_map.is_supported_file(std::path::Path::new("test.rs")));
        assert!(repo_map.is_supported_file(std::path::Path::new("main.py")));
        assert!(!repo_map.is_supported_file(std::path::Path::new("test.txt")));

        Ok(())
    }

    #[tokio::test]
    async fn test_context_generation() -> Result<()> {
        let mut repo_map = RepoMap::new(PathBuf::from("test"))?;

        let main_content = r#"
            pub fn main() {
                test_function();
            }
        "#
        .to_string();

        let lib_content = r#"
            pub fn test_function() {
                println!("test");
            }
        "#
        .to_string();

        repo_map
            .process_files(vec![
                (PathBuf::from("main.rs"), main_content),
                (PathBuf::from("lib.rs"), lib_content),
            ])
            .await?;

        let context = repo_map.get_context(&[PathBuf::from("main.rs")])?;
        assert!(context.contains("main.rs"));
        assert!(context.contains("function main"));

        Ok(())
    }

    #[tokio::test]
    async fn test_directory_context_snapshot() -> Result<()> {
        use std::collections::BTreeMap;

        // Set up deterministic test environment
        let test_root = PathBuf::from("/test/workspace");
        let mut repo_map = RepoMap::new(test_root.clone())?;

        // Fixed config for deterministic weights
        repo_map = repo_map.with_config(RepoMapConfig { token_budget: 4000, ..Default::default() });

        let src_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src");
        println!("\nScanning directory: {:?}", src_dir); // Debug
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

                println!("Adding file to map: {:?}", test_path); // Debug
                                                                 // Use canonical path string as key for deterministic ordering
                let key = test_path.to_string_lossy().to_string();
                file_map.insert(key, (test_path, content.replace("\r\n", "\n")));
            }
        }

        println!("\nProcessing {} files", file_map.len()); // Debug
                                                           // file_map conversion to Vec for processing
        let file_map: Vec<(PathBuf, String)> = file_map.into_values().collect();

        repo_map.process_files(file_map).await?;

        // Get importance scores
        let scores = repo_map.graph.calculate_importance(&[]);
        dbg!(&scores);

        // Get context
        let context = repo_map.get_context(&[])?;

        assert_snapshot!(context);

        Ok(())
    }
}
