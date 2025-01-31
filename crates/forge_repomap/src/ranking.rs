#[derive(Debug, Clone, PartialEq)]
pub struct PageRankConfig {
    pub max_iterations: usize,
    pub damping_factor: f64,
    pub tolerance: f64,
}

impl Default for PageRankConfig {
    fn default() -> Self {
        Self { max_iterations: 100, damping_factor: 0.85, tolerance: 1e-6 }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum EdgeType {
    Import,
    Call,
    Implementation,
    Inheritance,
    Use,
}

impl EdgeType {
    pub fn base_weight(&self) -> f64 {
        match self {
            EdgeType::Import => 0.5,
            EdgeType::Call => 0.8,
            EdgeType::Implementation => 1.0,
            EdgeType::Inheritance => 1.0,
            EdgeType::Use => 0.6,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct EdgeWeight {
    pub edge_type: EdgeType,
    pub weight: f64,
}

impl Default for EdgeWeight {
    fn default() -> Self {
        Self { edge_type: EdgeType::Use, weight: 1.0 }
    }
}

impl EdgeWeight {
    pub fn new(edge_type: EdgeType) -> Self {
        let weight = edge_type.base_weight();
        Self { edge_type, weight }
    }

    pub fn recalculate_weight(&mut self) {
        self.weight = self.edge_type.base_weight();
    }
}

pub struct PageRank {
    config: PageRankConfig,
    edge_weight_factor: f64,
}

impl PageRank {
    pub fn new(config: PageRankConfig) -> Self {
        Self { config, edge_weight_factor: 1.0 }
    }

    pub fn with_edge_weights(mut self, factor: f64) -> Self {
        self.edge_weight_factor = factor;
        self
    }

    pub fn has_converged(
        old_scores: &std::collections::HashMap<petgraph::graph::NodeIndex, f64>,
        new_scores: &std::collections::HashMap<petgraph::graph::NodeIndex, f64>,
        tolerance: f64,
    ) -> bool {
        old_scores.iter().all(|(node, old_score)| {
            if let Some(new_score) = new_scores.get(node) {
                (new_score - old_score).abs() < tolerance
            } else {
                false
            }
        })
    }

    pub fn calculate(
        &self,
        graph: &petgraph::Graph<std::path::PathBuf, EdgeWeight>,
    ) -> std::collections::HashMap<std::path::PathBuf, f64> {
        use petgraph::visit::EdgeRef;
        let mut scores = std::collections::HashMap::new();
        let mut old_scores = std::collections::HashMap::new();

        // Initialize scores
        for node in graph.node_indices() {
            scores.insert(node, 1.0 / graph.node_count() as f64);
            old_scores.insert(node, 0.0);
        }

        for _ in 0..self.config.max_iterations {
            old_scores = scores.clone();
            let mut new_scores = std::collections::HashMap::new();

            // Initialize new scores with damping factor
            for node in graph.node_indices() {
                new_scores.insert(
                    node,
                    (1.0 - self.config.damping_factor) / graph.node_count() as f64,
                );
            }

            // Update scores based on edges
            for node in graph.node_indices() {
                let out_edges: Vec<_> = graph.edges(node).collect();
                if !out_edges.is_empty() {
                    let score = scores[&node];
                    let total_weight: f64 = out_edges
                        .iter()
                        .map(|e| e.weight().weight * self.edge_weight_factor)
                        .sum();

                    for edge in out_edges {
                        let target = edge.target();
                        let weight = edge.weight().weight * self.edge_weight_factor;
                        let contribution = score * weight / total_weight;
                        *new_scores.entry(target).or_insert(0.0) +=
                            self.config.damping_factor * contribution;
                    }
                }
            }

            scores = new_scores;

            if Self::has_converged(&old_scores, &scores, self.config.tolerance) {
                break;
            }
        }

        // Convert node indices back to paths
        let mut result = std::collections::HashMap::new();
        for (node_idx, score) in scores {
            if let Some(path) = graph.node_weight(node_idx) {
                result.insert(path.clone(), score);
            }
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_edge_type_weights() {
        assert!(
            EdgeType::Implementation.base_weight() > EdgeType::Import.base_weight(),
            "Implementation edges should have higher weight than imports"
        );
    }

    #[test]
    fn test_enhanced_page_rank() {
        use std::path::PathBuf;

        use petgraph::Graph;

        let mut graph = Graph::new();
        let n1 = graph.add_node(PathBuf::from("a.rs"));
        let n2 = graph.add_node(PathBuf::from("b.rs"));
        let n3 = graph.add_node(PathBuf::from("c.rs"));

        graph.add_edge(n1, n2, EdgeWeight::new(EdgeType::Implementation));
        graph.add_edge(n2, n3, EdgeWeight::new(EdgeType::Call));
        graph.add_edge(n3, n1, EdgeWeight::new(EdgeType::Use));

        let page_rank = PageRank::new(PageRankConfig::default()).with_edge_weights(1.2);

        let scores = page_rank.calculate(&graph);
        assert_eq!(scores.len(), 3);
    }
}
