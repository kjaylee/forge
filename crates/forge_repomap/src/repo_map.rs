use std::collections::HashMap;
use std::path::{Path, PathBuf};

use crate::error::Error;
use crate::graph::DependencyGraph;
use crate::parser::Parser;
use crate::ranking::{PageRankConfig, SymbolReference};
use crate::symbol::Symbol;

/// A map of a repository's code structure and relationships.
///
/// RepoMap analyzes a repository to build a comprehensive understanding of its:
/// - Defined symbols (functions, classes, etc.)
/// - File dependencies and relationships
/// - Code structure and organization
///
/// This information is used to provide relevant context to LLMs when they need to
/// understand or modify code in the repository.
///
/// # Example
/// ```no_run
/// use std::path::PathBuf;
/// use forge_repomap::RepoMap;
///
/// let mut repo_map = RepoMap::new(PathBuf::from("./"), 1000).unwrap();
/// repo_map.analyze().unwrap();
///
/// // Get context about specific files
/// let context = repo_map.get_context(&[PathBuf::from("src/main.rs")]);
/// ```
pub struct RepoMap {
    /// Root path of the repository being analyzed
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

    pub fn analyze(&mut self) -> Result<(), Error> {
        let walker = forge_walker::Walker::new(self.root_path.clone());
        let entries = futures::executor::block_on(walker.get())
            .map_err(|e| Error::Io(std::io::Error::new(
                std::io::ErrorKind::Other,
                e.to_string(),
            )))?;
        
        for entry in entries {
            let path = Path::new(&entry.path);
            if !entry.is_dir && self.is_supported_file(path) {
                self.process_file(path)?;
            }
        }

        self.build_dependency_graph();
        Ok(())
    }

    fn is_supported_file(&self, path: &Path) -> bool {
        path.extension()
            .and_then(|ext| ext.to_str())
            .map(|ext| matches!(ext, "rs" | "js" | "py" | "ts" | "tsx"))
            .unwrap_or(false)
    }

    fn process_file(&mut self, path: &Path) -> Result<(), Error> {
        let content = std::fs::read_to_string(path)?;
        let symbols = self.parser.parse_file(path, &content)?;
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
                    self.graph.add_symbol_reference(file_path, &reference.path, symbol_ref);
                }
            }
        }
    }

    pub fn get_context(&self, focused_paths: &[PathBuf]) -> String {
        let importance_scores = self.graph.calculate_importance_with_focus(focused_paths);
        let mut context = String::new();

        // Add focused files first
        for path in focused_paths {
            if let Some(symbols) = self.files.get(path) {
                self.append_file_context(&mut context, path, symbols);
            }
        }

        // Add other important files until we hit the token budget
        let mut other_files: Vec<_> = self.files.iter()
            .filter(|(path, _)| !focused_paths.contains(path))
            .collect();

        other_files.sort_by(|(path_a, _), (path_b, _)| {
            let score_a = importance_scores.get(*path_a).unwrap_or(&0.0);
            let score_b = importance_scores.get(*path_b).unwrap_or(&0.0);
            score_b.partial_cmp(score_a).unwrap()
        });

        for (path, symbols) in other_files {
            if self.estimate_tokens(&context) >= self.token_budget {
                break;
            }
            self.append_file_context(&mut context, path, symbols);
        }

        context
    }

    fn append_file_context(&self, context: &mut String, path: &Path, symbols: &[Symbol]) {
        if !context.is_empty() {
            context.push_str("\n\n");
        }

        if let Some(rel_path) = path.strip_prefix(&self.root_path).ok() {
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

    fn estimate_tokens(&self, text: &str) -> usize {
        // Enhanced tokenization estimation
        let mut token_count = 0;
        
        // Common programming token patterns
        let patterns = [
            // Symbols that are usually separate tokens
            "->", "=>", "::", "//", "/*", "*/", "#{", "${",
            // Operators
            "+", "-", "*", "/", "=", "!", "|", "&", "<", ">",
            // Brackets and punctuation
            "(", ")", "[", "]", "{", "}", ",", ";", ".", ":",
        ];

        // Split into words and process each
        for word in text.split_whitespace() {
            // Add base word as one token
            token_count += 1;
            
            // Check for common programming patterns
            for pattern in &patterns {
                if word.contains(pattern) {
                    // Each pattern is counted as a separate token
                    token_count += word.matches(pattern).count();
                    
                    // Count non-empty parts around the pattern
                    let parts: Vec<_> = word.split(pattern)
                        .filter(|s| !s.is_empty())
                        .collect();
                    token_count += parts.len();
                }
            }
        }

        // Count line breaks as they often represent structural tokens
        token_count += text.matches('\n').count();
        
        // Add overhead for potential subtokenization
        token_count += token_count / 5;
        
        token_count
    }

    pub fn update_file(&mut self, path: &Path) -> Result<(), Error> {
        self.process_file(path)?;
        self.build_dependency_graph();
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_token_estimation() {
        let repo_map = RepoMap::new(PathBuf::from("."), 1000).unwrap();
        
        // Test simple text
        let simple = "Hello world";
        assert_eq!(repo_map.estimate_tokens(simple), 2);
        
        // Test code-like text
        let code = "fn test() -> Result<(), Error> {\n    println!(\"test\");\n}";
        let token_count = repo_map.estimate_tokens(code);
        assert!(token_count >= 20, "Expected at least 20 tokens, got {}", token_count);
        
        // Test operator splitting
        let ops = "a + b * c";
        let count = repo_map.estimate_tokens(ops);
        assert!(count >= 5, "Expected at least 5 tokens, got {}", count);
        
        // Test common patterns
        let patterns = "impl Trait for Type {}";
        let count = repo_map.estimate_tokens(patterns);
        assert!(count >= 5, "Expected at least 5 tokens, got {}", count);
        
        // Test with paths and type parameters
        let complex = "std::collections::HashMap<String, Vec<T>>";
        let count = repo_map.estimate_tokens(complex);
        assert!(count >= 10, "Expected at least 10 tokens, got {}", count);
    }
}