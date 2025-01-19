use std::collections::HashMap;
use std::path::{Path, PathBuf};
use petgraph::graph::{Graph, NodeIndex};
use petgraph::visit::EdgeRef;

/// Represents a graph of dependencies between files in a codebase.
/// 
/// This graph tracks relationships between files where one file depends on another
/// through imports, references, or other relationships. The graph is used to:
/// - Calculate file importance based on their connections
/// - Find related files for context expansion
/// - Identify dependency chains
pub struct DependencyGraph {
    /// The underlying graph structure where nodes are file paths
    graph: Graph<PathBuf, ()>,
    /// Mapping of file paths to their corresponding node indices for quick lookup
    node_indices: HashMap<PathBuf, NodeIndex>,
}

impl DependencyGraph {
    pub fn new() -> Self {
        Self {
            graph: Graph::new(),
            node_indices: HashMap::new(),
        }
    }

    pub fn add_node(&mut self, path: PathBuf) -> NodeIndex {
        if let Some(&idx) = self.node_indices.get(&path) {
            idx
        } else {
            let idx = self.graph.add_node(path.clone());
            self.node_indices.insert(path, idx);
            idx
        }
    }

    pub fn add_edge(&mut self, from: &Path, to: &Path) {
        let from_idx = self.add_node(from.to_path_buf());
        let to_idx = self.add_node(to.to_path_buf());
        
        if !self.graph.contains_edge(from_idx, to_idx) {
            self.graph.add_edge(from_idx, to_idx, ());
        }
    }

    pub fn calculate_importance(&self) -> HashMap<PathBuf, f64> {
        let mut importance = HashMap::new();
        let node_count = self.graph.node_count() as f64;

        // Simple PageRank-like algorithm
        for node_idx in self.graph.node_indices() {
            let incoming = self.graph.edges_directed(node_idx, petgraph::Direction::Incoming).count() as f64;
            let outgoing = self.graph.edges_directed(node_idx, petgraph::Direction::Outgoing).count() as f64;
            
            let score = (1.0 + incoming * 2.0 + outgoing) / node_count;
            
            if let Some(path) = self.graph.node_weight(node_idx) {
                importance.insert(path.clone(), score);
            }
        }

        importance
    }

    pub fn get_dependent_files(&self, path: &Path) -> Vec<PathBuf> {
        let mut result = Vec::new();
        
        if let Some(&node_idx) = self.node_indices.get(path) {
            for edge in self.graph.edges_directed(node_idx, petgraph::Direction::Incoming) {
                if let Some(dep_path) = self.graph.node_weight(edge.source()) {
                    result.push(dep_path.clone());
                }
            }
        }
        
        result
    }
}