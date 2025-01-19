use std::collections::HashMap;
use std::path::{Path, PathBuf};

use crate::error::Error;
use crate::graph::DependencyGraph;
use crate::parser::Parser;
use crate::symbol::Symbol;

pub struct RepoMap {
    root_path: PathBuf,
    files: HashMap<PathBuf, Vec<Symbol>>,
    graph: DependencyGraph,
    parser: Parser,
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

        // Add files and their dependencies to the graph
        for (file_path, symbols) in &self.files {
            for symbol in symbols {
                for reference in &symbol.references {
                    self.graph.add_edge(file_path, &reference.path);
                }
            }
        }
    }

    pub fn get_context(&self, focused_paths: &[PathBuf]) -> String {
        let importance_scores = self.graph.calculate_importance();
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
        // Rough estimation: ~4 chars per token
        text.len() / 4
    }

    pub fn update_file(&mut self, path: &Path) -> Result<(), Error> {
        self.process_file(path)?;
        self.build_dependency_graph();
        Ok(())
    }
}