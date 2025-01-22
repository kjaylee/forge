use std::path::{Path, PathBuf};
use petgraph::prelude::*;
use petgraph::algo::page_rank;
use std::collections::{HashMap, BTreeMap};
use crate::ranking::EdgeType;

pub struct DependencyGraph {
    graph: Graph<PathBuf, f64>,
    node_indices: BTreeMap<PathBuf, NodeIndex>,  // Changed to BTreeMap for deterministic ordering
    edge_to_type: HashMap<EdgeIndex, EdgeType>,
    total_weights: BTreeMap<PathBuf, f64>,  // Changed to BTreeMap for deterministic ordering
}

impl DependencyGraph {
    pub fn new() -> Self {
        Self {
            graph: Graph::new(),
            node_indices: BTreeMap::new(),
            edge_to_type: HashMap::new(),
            total_weights: BTreeMap::new(),
        }
    }

    pub fn add_node(&mut self, path: &Path) -> NodeIndex {
        if let Some(&idx) = self.node_indices.get(path) {
            idx
        } else {
            let idx = self.graph.add_node(path.to_path_buf());
            self.node_indices.insert(path.to_path_buf(), idx);
            self.total_weights.insert(path.to_path_buf(), 0.0);
            idx
        }
    }

    pub fn add_symbol_reference(
        &mut self,
        from: &Path,
        to: &Path,
        edge_type: EdgeType,
    ) {
        let from_idx = self.add_node(from);
        let to_idx = self.add_node(to);

        // Calculate edge weight based on reference type and frequency
        let weight = edge_type.base_weight();

        // Update total weights - track both incoming and outgoing
        *self.total_weights.entry(from.to_path_buf()).or_insert(0.0) += weight;
        *self.total_weights.entry(to.to_path_buf()).or_insert(0.0) += weight;

        if let Some(edge_idx) = self.graph.find_edge(from_idx, to_idx) {
            // If edge exists, update its weight
            if let Some(edge_weight) = self.graph.edge_weight_mut(edge_idx) {
                *edge_weight += weight;
            }
        } else {
            // Create new edge
            let edge_idx = self.graph.add_edge(from_idx, to_idx, weight);
            self.edge_to_type.insert(edge_idx, edge_type);
        }
    }

    pub fn calculate_importance(&self, focused_paths: &[PathBuf]) -> BTreeMap<PathBuf, f64> {  // Changed return type to BTreeMap
        // First pass: calculate total outgoing weights for each node
        let mut outgoing_weights: BTreeMap<NodeIndex, f64> = BTreeMap::new();  // Changed to BTreeMap
        
        // Process edges in deterministic order
        let mut edges: Vec<_> = self.graph.edge_references().collect();
        edges.sort_by_key(|e| (e.source(), e.target()));
        
        for edge in &edges {
            let source = edge.source();
            let weight = *edge.weight();
            *outgoing_weights.entry(source).or_insert(0.0) += weight;
        }

        // Create normalized graph
        let mut normalized_graph = Graph::new();
        let mut node_map = BTreeMap::new();  // Changed to BTreeMap

        // Add nodes in deterministic order
        let nodes: Vec<_> = self.graph.node_indices()
            .collect::<Vec<_>>();  // Collect once and reuse
        
        for &node_idx in &nodes {
            let new_idx = normalized_graph.add_node(self.graph[node_idx].clone());
            node_map.insert(node_idx, new_idx);
        }

        // Add edges in deterministic order
        for edge in &edges {
            let source = edge.source();
            let target = edge.target();
            let weight = *edge.weight();
            
            let total_weight = outgoing_weights.get(&source).unwrap_or(&1.0);
            let normalized_weight = if *total_weight > 0.0 { weight / total_weight } else { weight };
            
            let new_source = node_map[&source];
            let new_target = node_map[&target];
            normalized_graph.add_edge(new_source, new_target, normalized_weight);
        }

        // Calculate PageRank on normalized graph
        let ranks = page_rank(&normalized_graph, 0.85, 100);
        
        // Calculate maximum total weight for normalization
        let max_weight = self.total_weights.values().copied().fold(1.0_f64, f64::max);

        // Calculate scores in deterministic order
        let mut scores = BTreeMap::new();
        let focus_boost = if !focused_paths.is_empty() { 3.0 } else { 1.0 };
        
        for &node_idx in &nodes {
            if let Some(path) = self.graph.node_weight(node_idx) {
                let rank = ranks[node_map[&node_idx].index()];
                let total_weight = self.total_weights.get(path).unwrap_or(&0.0);
                let weight_factor = 1.0 + (total_weight / max_weight).sqrt(); // Use sqrt for smoother scaling
                let importance = rank * weight_factor;
                
                let multiplier = if focused_paths.contains(path) { focus_boost } else { 1.0 };
                scores.insert(path.clone(), importance * multiplier);
            }
        }

        // Normalize final scores
        let total_score: f64 = scores.values().sum();
        if total_score > 0.0 {
            for score in scores.values_mut() {
                *score /= total_score;
            }
        }

        scores
    }

    pub fn get_edge_info(&self, edge_idx: EdgeIndex) -> Option<(&EdgeType, f64)> {
        self.edge_to_type.get(&edge_idx).and_then(|edge_type| {
            self.graph
                .edge_weight(edge_idx)
                .map(|weight| (edge_type, *weight))
        })
    }

    pub fn get_graph(&self) -> &Graph<PathBuf, f64> {
        &self.graph
    }

    pub fn debug_print_state(&self) {
        println!("\nGraph State:");
        println!("Nodes: {}", self.graph.node_count());
        println!("Edges: {}", self.graph.edge_count());
        
        println!("\nNodes:");
        let mut nodes: Vec<_> = self.graph.node_indices().collect();
        nodes.sort();
        for node_idx in nodes {
            if let Some(path) = self.graph.node_weight(node_idx) {
                println!("{:?}: {:?}", node_idx, path);
            }
        }
        
        println!("\nEdges:");
        let mut edges: Vec<_> = self.graph.edge_references().collect();
        edges.sort_by_key(|e| (e.source(), e.target()));
        for edge in edges {
            let source = self.graph.node_weight(edge.source()).unwrap();
            let target = self.graph.node_weight(edge.target()).unwrap();
            let weight = edge.weight();
            println!("{:?} -> {:?} (weight: {})", source, target, weight);
        }

        println!("\nTotal weights per file:");
        for (path, weight) in &self.total_weights {  // BTreeMap is already ordered
            println!("{:?}: {}", path, weight);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add_symbol_reference() {
        let mut graph = DependencyGraph::new();
        let from = Path::new("src/lib.rs");
        let to = Path::new("src/module.rs");
        
        graph.add_symbol_reference(from, to, EdgeType::Call);
        
        assert_eq!(graph.node_indices.len(), 2);
    }

    #[test]
    fn test_multiple_references() {
        let mut graph = DependencyGraph::new();
        let from = Path::new("src/main.rs");
        let to = Path::new("src/lib.rs");

        // Add first reference
        graph.add_symbol_reference(from, to, EdgeType::Call);

        // Add second reference to same files with different type
        graph.add_symbol_reference(from, to, EdgeType::Implementation);

        // Should still only have 2 nodes
        assert_eq!(graph.node_indices.len(), 2);
    }

    #[test]
    fn test_importance_calculation() {
        let mut graph = DependencyGraph::new();
        let main = PathBuf::from("src/main.rs");
        let lib = PathBuf::from("src/lib.rs");
        let util = PathBuf::from("src/util.rs");

        // Create a graph where main.rs references lib.rs multiple times
        graph.add_symbol_reference(&main, &lib, EdgeType::Call);
        graph.add_symbol_reference(&main, &lib, EdgeType::Implementation);
        graph.add_symbol_reference(&main, &util, EdgeType::Use);
        graph.add_symbol_reference(&lib, &util, EdgeType::Use);

        let scores = graph.calculate_importance(&[]);
        
        // Check that scores are properly normalized
        let total_score: f64 = scores.values().sum();
        assert!((total_score - 1.0).abs() < 1e-6, "Scores should sum to 1.0");

        // Test focus boosting
        let focused_scores = graph.calculate_importance(&[main.clone()]);
        assert!(
            focused_scores.get(&main).unwrap() > scores.get(&main).unwrap(),
            "Focused file should have higher importance"
        );
    }

    #[test]
    fn test_weighted_importance() {
        let mut graph = DependencyGraph::new();
        let heavy = PathBuf::from("src/heavy.rs");
        let light = PathBuf::from("src/light.rs");
        let other = PathBuf::from("src/other.rs");

        // Add many references from heavy.rs
        for _ in 0..10 {
            graph.add_symbol_reference(&heavy, &other, EdgeType::Implementation);
        }

        // Add few references from light.rs
        graph.add_symbol_reference(&light, &other, EdgeType::Use);

        let scores = graph.calculate_importance(&[]);
        
        let heavy_score = scores.get(&heavy).unwrap();
        let light_score = scores.get(&light).unwrap();
        
        assert!(heavy_score > light_score,
            "File with more references should have higher importance: heavy({}) > light({})",
            heavy_score, light_score
        );
    }
}