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
    /// Root path of the repository being analyzed
    root_path: PathBuf,
    /// Map of file paths to their contained symbols
    files: HashMap<PathBuf, Vec<Symbol>>,
    /// Graph representing relationships between files
    graph: DependencyGraph,
    /// Parser for analyzing source code
    parser: Option<Parser>,
    /// Maximum number of tokens to include in context
    token_budget: usize,
}

impl RepoMap {
    pub fn new(root_path: PathBuf, token_budget: usize) -> Result<Self, Error> {
        Ok(Self {
            root_path,
            files: HashMap::new(),
            graph: DependencyGraph::new(),
            parser: None,
            token_budget,
        })
    }

    pub fn with_parser(mut self) -> Result<Self, Error> {
        self.parser = Some(Parser::new()?);
        Ok(self)
    }

    /// Configure PageRank parameters for importance calculation
    pub fn with_page_rank_config(mut self, config: PageRankConfig) -> Self {
        self.graph = self.graph.with_page_rank_config(config);
        self
    }

    pub fn analyze(&mut self) -> Result<(), Error> {
        let parser = self.parser.as_ref().ok_or_else(|| {
            Error::Parse("Parser not initialized. Call with_parser() first".to_string())
        })?;

        let walker = forge_walker::Walker::new(self.root_path.clone());
        let entries = futures::executor::block_on(walker.get()).map_err(|e| {
            Error::Io(std::io::Error::new(
                std::io::ErrorKind::Other,
                e.to_string(),
            ))
        })?;

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
        let parser = self.parser.as_ref().ok_or_else(|| {
            Error::Parse("Parser not initialized. Call with_parser() first".to_string())
        })?;

        let content = std::fs::read_to_string(path)?;
        let symbols = parser.parse_file(path, &content)?;
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
        let importance_scores = self.graph.calculate_importance_with_focus(focused_paths);
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

    pub fn update_file(&mut self, path: &Path) -> Result<(), Error> {
        self.process_file(path)?;
        self.build_dependency_graph();
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    
}
