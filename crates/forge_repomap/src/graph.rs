use std::collections::HashMap;
use std::path::{Path, PathBuf};

use petgraph::graph::{Graph, NodeIndex};
use petgraph::visit::EdgeRef;

use crate::ranking::{EdgeWeight, PageRank, PageRankConfig, SymbolReference};

/// Represents a graph of dependencies between files in a codebase.
///
/// This graph tracks relationships between files where one file depends on
/// another through imports, references, or other relationships. The graph is
/// used to:
/// - Calculate file importance based on their connections
/// - Find related files for context expansion
/// - Identify dependency chains
pub struct DependencyGraph {
    /// The underlying graph structure where nodes are file paths
    graph: Graph<PathBuf, EdgeWeight>,
    /// Mapping of file paths to their corresponding node indices for quick
    /// lookup
    node_indices: HashMap<PathBuf, NodeIndex>,
    /// PageRank configuration
    page_rank_config: PageRankConfig,
}

impl DependencyGraph {
    pub fn new() -> Self {
        Self {
            graph: Graph::new(),
            node_indices: HashMap::new(),
            page_rank_config: PageRankConfig::default(),
        }
    }

    /// Configure PageRank parameters
    pub fn with_page_rank_config(mut self, config: PageRankConfig) -> Self {
        self.page_rank_config = config;
        self
    }

    pub fn add_node(&mut self, path: PathBuf) -> NodeIndex {
        if let Some(&idx) = self.node_indices.get(&path) {
            idx
        } else {
            let idx = self.graph.add_node(path.clone());
            self.node_indices.insert(path.clone(), idx);
            idx
        }
    }

    /// Initialize or update node weight, returns the calculated weight    /// Add a symbol reference between two files
    pub fn add_symbol_reference(&mut self, from: &Path, to: &Path, symbol: SymbolReference) {
        let from_idx = self.add_node(from.to_path_buf());
        let to_idx = self.add_node(to.to_path_buf());

        let edge = if let Some(edge_idx) = self.graph.find_edge(from_idx, to_idx) {
            edge_idx
        } else {
            self.graph.add_edge(from_idx, to_idx, EdgeWeight::default())
        };

        if let Some(weight) = self.graph.edge_weight_mut(edge) {
            weight.symbol_refs.push(symbol);
            weight.weight = weight
                .symbol_refs
                .iter()
                .map(|s| s.kind.base_weight() * s.count as f64)
                .sum::<f64>();
        }
    }

    /// Calculate importance scores with emphasized files
    pub fn calculate_importance(&self, focused_files: &[PathBuf]) -> HashMap<PathBuf, f64> {
        let mut personalization = HashMap::new();
        let mut importance_scores = HashMap::new();
        // If there are no nodes, just bail out with empty scores
        if self.graph.node_count() == 0 {
            return importance_scores;
        }

        let default_weight = 1.0 / self.graph.node_count() as f64;
        let focus_weight = 4.0 * default_weight; // Focused files get 4x weight

        // Initialize scores
        for node_idx in self.graph.node_indices() {
            if let Some(path) = self.graph.node_weight(node_idx) {
                importance_scores.insert(path.clone(), default_weight);
                if focused_files.contains(path) {
                    personalization.insert(path.clone(), focus_weight);
                }
            }
        }

        // Calculate base reference-weighted scores
        for edge in self.graph.edge_references() {
            if let (Some(_from_path), Some(to_path)) = (
                self.graph.node_weight(edge.source()),
                self.graph.node_weight(edge.target()),
            ) {
                let weight = edge.weight();
                let score = weight.symbol_refs.iter()
                    .map(|s| s.kind.base_weight() * s.count as f64)
                    .sum::<f64>();
                
                // Add weighted score to the target file
                *importance_scores.entry(to_path.clone()).or_insert(0.0) += score;
            }
        }

        // Calculate PageRank using initial scores and personalization
        let page_rank = PageRank::new(self.page_rank_config.clone());
        let pr_scores = page_rank.calculate(&self.graph, Some(&personalization));

        // Combine reference-based scores with PageRank
        for (path, pr_score) in pr_scores {
            let ref_score = importance_scores.get(&path).unwrap_or(&0.0);
            importance_scores.insert(path, (pr_score + ref_score) / 2.0);
        }

        // Normalize scores
        let max_score = importance_scores.values().fold(0.0_f64, |a, &b| a.max(b));
        if max_score > 0.0 {
            for score in importance_scores.values_mut() {
                *score /= max_score;
            }
        }

        importance_scores
    }

}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::*;
    use crate::symbol::SymbolKind;

    #[test]
    fn test_add_symbol_reference() {
        let mut graph = DependencyGraph::new();
        let symbol = SymbolReference {
            name: Rc::new("test_fn".to_string()),
            kind: SymbolKind::Function,
            count: 1,
        };

        graph.add_symbol_reference(Path::new("src/main.rs"), Path::new("src/lib.rs"), symbol);

        // Check if edge exists with correct weight
        let main_idx = graph.node_indices[&PathBuf::from("src/main.rs")];
        let lib_idx = graph.node_indices[&PathBuf::from("src/lib.rs")];

        let edge = graph.graph.find_edge(main_idx, lib_idx).unwrap();
        let weight = graph.graph.edge_weight(edge).unwrap();

        assert_eq!(weight.symbol_refs.len(), 1);
        assert_eq!(weight.weight, SymbolKind::Function.base_weight());
    }

    #[test]
    fn test_symbol_reference_importance() {
        let mut graph = DependencyGraph::new();

        // Add multiple references with different weights
        let function_ref = SymbolReference {
            name: Rc::new("test_fn".to_string()),
            kind: SymbolKind::Function,
            count: 3, // Called multiple times
        };

        let trait_ref = SymbolReference {
            name: Rc::new("TestTrait".to_string()),
            kind: SymbolKind::Trait,
            count: 1,
        };

        let var_ref = SymbolReference {
            name: Rc::new("test_var".to_string()),
            kind: SymbolKind::Variable,
            count: 1,
        };

        // a.rs -> b.rs (multiple function calls)
        graph.add_symbol_reference(
            Path::new("src/a.rs"), 
            Path::new("src/b.rs"), 
            function_ref.clone()
        );

        // b.rs -> c.rs (trait reference)
        graph.add_symbol_reference(
            Path::new("src/b.rs"), 
            Path::new("src/c.rs"), 
            trait_ref
        );

        // b.rs -> d.rs (variable reference)
        graph.add_symbol_reference(
            Path::new("src/b.rs"), 
            Path::new("src/d.rs"), 
            var_ref
        );

        let scores = graph.calculate_importance(&[]);

        // b.rs should have higher score due to multiple incoming function references
        let b_score = scores[&PathBuf::from("src/b.rs")];
        let d_score = scores[&PathBuf::from("src/d.rs")];

        assert!(b_score > d_score, 
            "b.rs (score: {}) should have higher score than d.rs (score: {})", 
            b_score, d_score);

        // c.rs should have higher score than d.rs due to trait reference
        let c_score = scores[&PathBuf::from("src/c.rs")];
        assert!(c_score > d_score,
            "c.rs (score: {}) should have higher score than d.rs (score: {}) due to trait reference",
            c_score, d_score);
    }

    #[test]
    fn test_focused_importance() {
        let mut graph = DependencyGraph::new();

        // Create a chain of references with module symbols (higher weight)
        let symbol = SymbolReference {
            name: Rc::new("test_module".to_string()),
            kind: SymbolKind::Module, // Higher weight symbol
            count: 2,                 // More references
        };

        // Create a cycle of references to make the graph more connected
        graph.add_symbol_reference(Path::new("src/a.rs"), Path::new("src/b.rs"), symbol.clone());

        graph.add_symbol_reference(Path::new("src/b.rs"), Path::new("src/a.rs"), symbol.clone());

        // Add a reference to c.rs with lower weight
        let weak_symbol = SymbolReference {
            name: Rc::new("test_var".to_string()),
            kind: SymbolKind::Variable, // Lower weight symbol
            count: 1,
        };

        graph.add_symbol_reference(Path::new("src/b.rs"), Path::new("src/c.rs"), weak_symbol);

        // Focus on a.rs
        let mut scores = graph.calculate_importance(&[PathBuf::from("src/a.rs")]);

        // Normalize scores for comparison
        let sum: f64 = scores.values().sum();
        for score in scores.values_mut() {
            *score /= sum;
        }

        // a.rs should have highest normalized score
        let a_score = scores[&PathBuf::from("src/a.rs")];
        let c_score = scores[&PathBuf::from("src/c.rs")];

        assert!(
            a_score > c_score,
            "Score for a.rs ({}) should be greater than c.rs ({})",
            a_score,
            c_score
        );
    }
}
