use std::collections::HashMap;
use std::path::PathBuf;
use petgraph::graph::{Graph, NodeIndex};
use petgraph::visit::EdgeRef;
use crate::symbol;

/// Configuration for PageRank calculation
#[derive(Debug, Clone)]
pub struct PageRankConfig {
    /// Damping factor (typically 0.85)
    pub damping_factor: f64,
    /// Maximum number of iterations
    pub max_iterations: usize,
    /// Convergence tolerance
    pub tolerance: f64,
}

impl Default for PageRankConfig {
    fn default() -> Self {
        Self {
            damping_factor: 0.85,
            max_iterations: 100,
            tolerance: 1e-6,
        }
    }
}

/// Edge weight containing symbol references and their weights
#[derive(Debug, Clone)]
pub struct EdgeWeight {
    /// Total weight of the edge
    pub weight: f64,
    /// References to symbols that create this relationship
    pub symbol_refs: Vec<SymbolReference>,
}

impl Default for EdgeWeight {
    fn default() -> Self {
        Self {
            weight: 1.0,
            symbol_refs: Vec::new(),
        }
    }
}

/// A reference to a symbol that creates a relationship between files
#[derive(Debug, Clone)]
pub struct SymbolReference {
    /// Name of the symbol
    pub name: String,
    /// Kind of symbol (function, class, etc.)
    pub kind: symbol::SymbolKind,
    /// Number of times this symbol is referenced
    pub count: usize,
}

impl SymbolReference {
    /// Get the base weight for this symbol reference
    pub fn base_weight(&self) -> f64 {
        let kind_weight = match self.kind {
            symbol::SymbolKind::Module => 1.5,       // Highest weight for modules
            symbol::SymbolKind::Trait => 1.4,        // Traits are important for Rust
            symbol::SymbolKind::Interface => 1.4,    // Interfaces are important
            symbol::SymbolKind::Class => 1.3,        // Classes define major structures
            symbol::SymbolKind::Struct => 1.3,       // Structs are like classes
            symbol::SymbolKind::Enum => 1.2,         // Enums define important types
            symbol::SymbolKind::Function => 1.1,     // Functions are common but important
            symbol::SymbolKind::Method => 1.1,       // Methods are like functions
            symbol::SymbolKind::Implementation => 1.1, // Implementations are important
            symbol::SymbolKind::Constant => 0.9,     // Constants are referenced but simple
            symbol::SymbolKind::Variable => 0.8,     // Variables have lowest weight
        };

        kind_weight * (1.0 + (self.count as f64).ln().max(0.0))
    }
}

/// Implementation of PageRank algorithm for dependency graphs
pub struct PageRank {
    config: PageRankConfig,
}

impl PageRank {
    pub fn new(config: PageRankConfig) -> Self {
        Self { config }
    }

    /// Calculate PageRank scores for nodes in the graph
    pub fn calculate(
        &self,
        graph: &Graph<PathBuf, EdgeWeight>,
        personalization: Option<&HashMap<PathBuf, f64>>,
    ) -> HashMap<PathBuf, f64> {
        let n = graph.node_count();
        if n == 0 {
            return HashMap::new();
        }

        // Initialize scores
        let mut scores: HashMap<NodeIndex, f64> = graph
            .node_indices()
            .map(|idx| (idx, 1.0 / n as f64))
            .collect();

        // Create personalization vector if provided
        let pers: HashMap<NodeIndex, f64> = if let Some(p) = personalization {
            graph
                .node_indices()
                .filter_map(|idx| {
                    graph
                        .node_weight(idx)
                        .and_then(|path| p.get(path))
                        .map(|&w| (idx, w))
                })
                .collect()
        } else {
            HashMap::new()
        };

        // Normalize personalization scores
        let default_score = 1.0 / n as f64;
        
        // Iterative calculation
        for _ in 0..self.config.max_iterations {
            let mut new_scores: HashMap<NodeIndex, f64> = HashMap::new();
            
            // Calculate new score for each node
            for node in graph.node_indices() {
                let mut score = 0.0;
                
                // Sum weighted contributions from incoming edges
                for edge in graph.edges_directed(node, petgraph::Direction::Incoming) {
                    let source = edge.source();
                    let source_score = scores[&source];
                    let weight = edge.weight().weight;
                    
                    // Get number of outgoing edges from source
                    let source_out_degree: f64 = graph
                        .edges_directed(source, petgraph::Direction::Outgoing)
                        .map(|e| e.weight().weight)
                        .sum();
                    
                    if source_out_degree > 0.0 {
                        score += source_score * weight / source_out_degree;
                    }
                }
                
                // Apply damping factor
                score = (1.0 - self.config.damping_factor) * (pers.get(&node).unwrap_or(&default_score))
                    + self.config.damping_factor * score;
                
                new_scores.insert(node, score);
            }
            
            // Check for convergence
            if self.has_converged(&scores, &new_scores) {
                scores = new_scores;
                break;
            }
            
            scores = new_scores;
        }

        // Convert NodeIndex scores to PathBuf scores
        scores
            .into_iter()
            .filter_map(|(idx, score)| {
                graph.node_weight(idx).map(|path| (path.clone(), score))
            })
            .collect()
    }

    /// Check if PageRank scores have converged
    fn has_converged(
        &self,
        old_scores: &HashMap<NodeIndex, f64>,
        new_scores: &HashMap<NodeIndex, f64>,
    ) -> bool {
        old_scores.iter().all(|(idx, &old_score)| {
            let new_score = new_scores.get(idx).unwrap_or(&0.0);
            (new_score - old_score).abs() < self.config.tolerance
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use petgraph::Graph;
    use crate::symbol::SymbolKind;

    #[test]
    fn test_page_rank_simple_graph() {
        let mut graph = Graph::new();
        
        // Create a simple graph with 3 nodes
        let n1 = graph.add_node(PathBuf::from("a.rs"));
        let n2 = graph.add_node(PathBuf::from("b.rs"));
        let n3 = graph.add_node(PathBuf::from("c.rs"));
        
        // Add edges with weights
        graph.add_edge(n1, n2, EdgeWeight::default());
        graph.add_edge(n2, n3, EdgeWeight::default());
        graph.add_edge(n3, n1, EdgeWeight::default());
        
        let config = PageRankConfig::default();
        let page_rank = PageRank::new(config);
        let scores = page_rank.calculate(&graph, None);
        
        // In this symmetric graph, all scores should be approximately equal
        assert_eq!(scores.len(), 3);
        let first_score = scores.values().next().unwrap();
        for score in scores.values() {
            assert!((score - first_score).abs() < 0.01);
        }
    }

    #[test]
    fn test_page_rank_with_personalization() {
        let mut graph = Graph::new();
        
        // Create nodes
        let n1 = graph.add_node(PathBuf::from("a.rs"));
        let n2 = graph.add_node(PathBuf::from("b.rs"));
        let n3 = graph.add_node(PathBuf::from("c.rs"));
        
        // Add edges
        graph.add_edge(n1, n2, EdgeWeight::default());
        graph.add_edge(n2, n3, EdgeWeight::default());
        
        // Create personalization vector favoring a.rs
        let mut pers = HashMap::new();
        pers.insert(PathBuf::from("a.rs"), 0.8);
        pers.insert(PathBuf::from("b.rs"), 0.1);
        pers.insert(PathBuf::from("c.rs"), 0.1);
        
        let config = PageRankConfig::default();
        let page_rank = PageRank::new(config);
        let scores = page_rank.calculate(&graph, Some(&pers));
        
        // a.rs should have highest score
        let a_score = scores.get(&PathBuf::from("a.rs")).unwrap();
        for (path, score) in scores.iter() {
            if path != &PathBuf::from("a.rs") {
                assert!(score < a_score);
            }
        }
    }

    #[test]
    fn test_symbol_weights() {
        let module_ref = SymbolReference {
            name: "test".to_string(),
            kind: SymbolKind::Module,
            count: 1,
        };
        let variable_ref = SymbolReference {
            name: "test".to_string(),
            kind: SymbolKind::Variable,
            count: 1,
        };
        
        assert!(module_ref.base_weight() > variable_ref.base_weight());
    }

    #[test]
    fn test_reference_count_weight() {
        let ref1 = SymbolReference {
            name: "test".to_string(),
            kind: SymbolKind::Function,
            count: 1,
        };
        let ref2 = SymbolReference {
            name: "test".to_string(),
            kind: SymbolKind::Function,
            count: 10,
        };
        
        assert!(ref2.base_weight() > ref1.base_weight());
    }
}