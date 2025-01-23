use std::collections::{HashSet};
use std::path::PathBuf;

use super::graph::ReferenceGraph;
use super::symbol::{Symbol, SymbolIndex};

pub struct SymbolRanker<'a> {
    symbol_index: &'a SymbolIndex,
    reference_graph: ReferenceGraph,
}

impl<'a> SymbolRanker<'a> {
    pub fn new(symbol_index: &'a SymbolIndex) -> Self {
        let reference_graph = ReferenceGraph::from_symbol_index(symbol_index, &HashSet::new());
        Self {
            symbol_index,
            reference_graph,
        }
    }

    pub fn get_ranked_symbols(&mut self) -> Vec<Symbol> {
        self.reference_graph.calculate_and_distribute_ranks();

        let sorted_definitions = self.reference_graph.get_sorted_definitions();

        let graph = self.reference_graph.get_graph();

        let mut symbols = vec![];

        for ((node, name), _rank) in sorted_definitions {
            let path = PathBuf::from(&graph[*node]);
            if let Some(definition) = self.symbol_index.definitions.get(&(path, name.clone())) {
                symbols.extend(definition.to_owned());
            }
        }

        symbols
    }
}