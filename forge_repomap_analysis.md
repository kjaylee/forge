# Forge RepoMap Analysis and Improvement Plan

## Sidecar Implementation Analysis

The sidecar implementation has several key advantages in terms of reference handling and tag management:

1. Tag Index System
```rust
pub struct TagIndex {
    // Maps tag names to definition file paths
    pub defines: HashMap<String, HashSet<PathBuf>>,
    // Maps tag names to reference file paths
    pub references: HashMap<String, Vec<PathBuf>>,
    // Maps (file path, tag name) to tag definitions
    pub definitions: HashMap<(PathBuf, String), HashSet<Tag>>,
    // Set of commonly used tags
    pub common_tags: HashSet<String>,
    // Maps files to their tags
    pub file_to_tags: HashMap<PathBuf, HashSet<(PathBuf, String)>>,
}
```

2. Advanced Graph-based Ranking System
```rust
pub struct TagGraph {
    graph: DiGraph<String, f64>,
    node_indices: HashMap<String, NodeIndex>,
    edge_to_ident: HashMap<EdgeIndex, String>,
    ranked_definitions: RankedDefinitionsMap,
    sorted_definitions: Vec<RankedDefinition>,
}
```

3. Comprehensive Tag Processing
- Parallel tag generation using async/await
- Support for multiple programming languages
- Reference tracking and importance calculation
- Page rank-based relevance scoring

## Current Implementation Gaps

Our current implementation is missing several key features compared to the sidecar version:

1. No Comprehensive Tag Index
   - We lack proper mapping between definitions and references
   - No tracking of common tags
   - Missing file-to-tags relationship mapping

2. Limited Reference Resolution
   - Only basic reference capture
   - No cross-file reference tracking
   - Missing scope-aware reference resolution

3. Simple Graph Structure
   - Basic dependency graph without weights
   - No PageRank implementation
   - Missing edge importance calculations

4. Limited Language Support
   - Basic tree-sitter integration
   - Missing comprehensive query patterns
   - Limited language-specific features

## Required Changes

### 1. Enhanced Tag Index System

```rust
pub struct TagIndex {
    // Maps symbol names to their definition locations
    defines: HashMap<String, HashSet<PathBuf>>,
    // Maps symbol names to their reference locations
    references: HashMap<String, Vec<PathBuf>>,
    // Maps (file, symbol) pairs to actual symbols
    definitions: HashMap<(PathBuf, String), HashSet<Symbol>>,
    // Frequently referenced symbols
    common_symbols: HashSet<String>,
    // Maps files to their contained symbols
    file_symbols: HashMap<PathBuf, HashSet<(PathBuf, String)>>,
    // Root path for relative path calculations
    root_path: PathBuf,
}

impl TagIndex {
    pub fn process_references(&mut self) {
        // Handle symbols without explicit references
        if self.references.is_empty() {
            self.references = self.defines
                .iter()
                .map(|(k, v)| (k.clone(), v.iter().cloned().collect()))
                .collect();
        }

        // Identify commonly used symbols
        self.common_symbols = self.defines
            .keys()
            .filter(|key| self.references.contains_key(*key))
            .cloned()
            .collect();
    }
}
```

### 2. Improved Graph Implementation

```rust
pub struct DependencyGraph {
    graph: DiGraph<String, f64>,
    node_map: HashMap<String, NodeIndex>,
    edge_weights: HashMap<EdgeIndex, String>,
    ranked_nodes: HashMap<(NodeIndex, String), f64>,
}

impl DependencyGraph {
    pub fn calculate_importance(&mut self) -> HashMap<PathBuf, f64> {
        // Calculate PageRank scores
        let ranks = page_rank(&self.graph, 0.85, 0.001);
        
        // Distribute ranks based on edge weights
        let mut importance = HashMap::new();
        for (idx, rank) in ranks.iter().enumerate() {
            let node = &self.graph[NodeIndex::new(idx)];
            importance.insert(PathBuf::from(node), *rank);
        }
        
        importance
    }

    pub fn add_reference(&mut self, from: &Path, to: &Path, weight: f64) {
        let from_idx = self.get_or_create_node(from.to_str().unwrap());
        let to_idx = self.get_or_create_node(to.to_str().unwrap());
        
        let edge = self.graph.add_edge(from_idx, to_idx, weight);
        self.edge_weights.insert(edge, from.to_str().unwrap().to_string());
    }
}
```

### 3. Enhanced Parser Implementation

```rust
impl Parser {
    pub fn parse_file(&self, path: &Path, content: &str) -> Result<Vec<Symbol>, Error> {
        let language = self.detect_language(path)?;
        let lang = self.parsers.get(language)?;
        let parser = self.prepare_parser(lang)?;
        let tree = parser.parse(content, None)?;
        let query = self.queries.get(language)?;

        let mut symbols = Vec::new();
        let mut query_cursor = tree_sitter::QueryCursor::new();
        let matches = query_cursor.matches(query, tree.root_node(), content.as_bytes());

        for match_ in matches {
            for capture in match_.captures {
                let name = &query.capture_names()[capture.index as usize];
                let node = capture.node;

                match name.as_str() {
                    name if name.starts_with("name.definition.") => {
                        if let Some(symbol) = self.create_symbol(name, node, path, content)? {
                            symbols.push(symbol);
                        }
                    },
                    name if name.starts_with("name.reference.") => {
                        if let Some(reference) = self.create_reference(name, node, path, content)? {
                            // Store reference for later resolution
                            self.store_reference(reference);
                        }
                    },
                    _ => continue,
                }
            }
        }

        Ok(symbols)
    }

    fn create_reference(&self, 
                       capture_name: &str, 
                       node: Node, 
                       path: &Path, 
                       content: &str) -> Result<Reference, Error> {
        // Extract reference information
        let name = node.utf8_text(content.as_bytes())?.to_string();
        let kind = match &capture_name["name.reference.".len()..] {
            "call" => ReferenceKind::Call,
            "type" => ReferenceKind::Type,
            "implementation" => ReferenceKind::Implementation,
            _ => ReferenceKind::Other,
        };

        Ok(Reference {
            name,
            kind,
            location: Location::from_node(node, path),
        })
    }
}
```

### 4. Enhanced Tree-Sitter Queries

Example improved Rust query:
```scheme
; Definitions
(struct_item
    name: (type_identifier) @name.definition.struct
    body: (field_declaration_list)? @struct.body) @definition.struct

(impl_item
    trait: (type_identifier)? @impl.trait
    type: (type_identifier) @impl.type) @definition.implementation

; References
(type_identifier) @name.reference.type
(scoped_identifier
    path: (identifier) @reference.qualifier
    name: (identifier) @name.reference.qualified)

; Imports
(use_declaration
    path: (scoped_identifier) @import.path) @import

; Function Calls
(call_expression
    function: [
        (identifier) @name.reference.call
        (field_expression
            field: (field_identifier) @name.reference.call)
    ]) @reference.call
```

## Implementation Plan

1. Phase 1: Tag Index System (2-3 days)
   - Implement comprehensive TagIndex structure
   - Add reference tracking
   - Add file-to-symbol mapping
   - Add common symbol tracking
   - Add tests for tag index functionality

2. Phase 2: Graph System (2-3 days)
   - Implement weighted dependency graph
   - Add PageRank calculation
   - Add reference importance calculation
   - Add graph visualization helpers
   - Add tests for graph algorithms

3. Phase 3: Parser Enhancements (3-4 days)
   - Update tree-sitter query patterns
   - Add reference capture
   - Add scope tracking
   - Add import handling
   - Add tests for parsing features

4. Phase 4: Integration (2-3 days)
   - Connect all components
   - Add performance optimizations
   - Add parallel processing
   - Add comprehensive tests
   - Add documentation

## Testing Strategy

1. Unit Tests
```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tag_index() {
        let mut index = TagIndex::new(Path::new("/test"));
        
        // Test definition tracking
        index.add_tag(create_test_tag("test_fn", TagKind::Definition), 
                     &PathBuf::from("test.rs"));
        
        // Test reference tracking
        index.add_tag(create_test_tag("test_fn", TagKind::Reference),
                     &PathBuf::from("other.rs"));
        
        // Verify relationships
        assert!(index.defines.contains_key("test_fn"));
        assert!(index.references.contains_key("test_fn"));
        assert!(index.common_tags.contains("test_fn"));
    }

    #[test]
    fn test_graph_ranking() {
        let mut graph = DependencyGraph::new();
        
        // Add test nodes and edges
        graph.add_reference(
            Path::new("a.rs"),
            Path::new("b.rs"),
            1.0
        );
        
        // Calculate importance
        let importance = graph.calculate_importance();
        
        // Verify rankings
        assert!(importance.get(Path::new("b.rs")) > 
                importance.get(Path::new("a.rs")));
    }
}
```

2. Integration Tests
```rust
#[cfg(test)]
mod tests {
    #[tokio::test]
    async fn test_full_analysis() {
        let test_files = vec![
            ("test.rs", "fn test() { other() }"),
            ("other.rs", "fn other() {}")
        ];
        
        let repo_map = RepoMap::new()
            .with_map_tokens(1000)
            .analyze_files(test_files)
            .await;
            
        let context = repo_map.get_context(&[
            PathBuf::from("test.rs")
        ])?;
        
        assert!(context.contains("fn test"));
        assert!(context.contains("fn other"));
    }
}
```

## Performance Considerations

1. Parallel Processing
   - Use async/await for file operations
   - Implement parallel tag generation
   - Use thread pools for CPU-intensive tasks

2. Memory Optimization
   - Use reference counting for shared data
   - Implement efficient graph storage
   - Optimize string storage

3. Caching
   - Cache parsed trees
   - Cache query results
   - Cache calculated rankings

## Conclusion

The sidecar implementation provides several valuable insights for improving our forge_repomap:
1. Better reference tracking through comprehensive tag indexing
2. More accurate importance calculation using PageRank
3. Better parallelization of processing
4. More comprehensive language support

By implementing these improvements, we can create a more robust and efficient code analysis system.