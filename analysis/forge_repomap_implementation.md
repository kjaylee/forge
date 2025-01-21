# Forge RepoMap Implementation Plan

## Phase 1: Core Infrastructure

### 1. Token Management System
```rust
pub struct TokenManager {
    model: String,
    token_limit: usize,
    encoding: tiktoken::Encoding,
}

impl TokenManager {
    pub fn new(model: &str) -> Self;
    pub fn count_tokens(&self, text: &str) -> usize;
    pub fn is_within_limit(&self, text: &str) -> bool;
    pub fn get_truncated_text(&self, text: &str, limit: usize) -> String;
}
```

### 2. File System Abstraction
```rust
pub trait FileSystemProvider: Send + Sync {
    fn read_file(&self, path: &Path) -> Result<Vec<u8>, RepoMapError>;
    fn list_files(&self, path: &Path) -> Result<Vec<PathBuf>, RepoMapError>;
    fn get_file_info(&self, path: &Path) -> Result<FileInfo, RepoMapError>;
}

pub struct FileInfo {
    pub size: u64,
    pub modified: SystemTime,
    pub file_type: FileType,
}
```

### 3. Tree Generation
```rust
pub trait TreeBuilder {
    fn build(&self, config: &TreeConfig) -> Result<RepoTree, RepoMapError>;
    fn add_node(&mut self, node: TreeNode) -> Result<(), RepoMapError>;
    fn optimize(&mut self, token_limit: usize) -> Result<(), RepoMapError>;
}

pub struct TreeNode {
    pub path: PathBuf,
    pub content: String,
    pub metadata: NodeMetadata,
    pub children: Vec<TreeNode>,
}
```

## Phase 2: Enhanced Analysis

### 1. Semantic Analysis
```rust
pub trait SemanticAnalyzer {
    fn analyze_file(&self, content: &str, path: &Path) -> Result<SemanticInfo, RepoMapError>;
    fn detect_patterns(&self, info: &SemanticInfo) -> Vec<Pattern>;
    fn extract_relationships(&self, info: &SemanticInfo) -> Vec<Relationship>;
}

pub struct SemanticInfo {
    pub imports: Vec<Import>,
    pub definitions: Vec<Definition>,
    pub usages: Vec<Usage>,
    pub complexity: ComplexityMetrics,
}
```

### 2. Graph Analysis
```rust
pub trait GraphAnalyzer {
    fn build_graph(&self, relationships: &[Relationship]) -> Result<CodeGraph, RepoMapError>;
    fn calculate_importance(&self, graph: &CodeGraph) -> HashMap<NodeId, f64>;
    fn find_clusters(&self, graph: &CodeGraph) -> Vec<Cluster>;
}

pub struct CodeGraph {
    pub nodes: Vec<Node>,
    pub edges: Vec<Edge>,
    pub metadata: GraphMetadata,
}
```

### 3. Export System
```rust
pub trait Exporter {
    fn export(&self, tree: &RepoTree, format: ExportFormat) -> Result<String, RepoMapError>;
    fn get_supported_formats(&self) -> Vec<ExportFormat>;
}

pub enum ExportFormat {
    Markdown,
    Json,
    Dot,
    Mermaid,
    Custom(String),
}
```

## Phase 3: Optimization & Integration

### 1. Caching System
```rust
pub trait CacheProvider {
    fn get(&self, key: &str) -> Option<CachedData>;
    fn set(&self, key: &str, data: CachedData) -> Result<(), RepoMapError>;
    fn invalidate(&self, key: &str) -> Result<(), RepoMapError>;
}

pub struct CachedData {
    pub content: Vec<u8>,
    pub metadata: CacheMetadata,
    pub expiry: SystemTime,
}
```

### 2. Version Control Integration
```rust
pub trait VcsProvider {
    fn get_file_history(&self, path: &Path) -> Result<Vec<Commit>, RepoMapError>;
    fn get_blame_info(&self, path: &Path) -> Result<BlameInfo, RepoMapError>;
    fn get_change_frequency(&self, path: &Path) -> Result<ChangeFrequency, RepoMapError>;
}
```

### 3. Performance Monitoring
```rust
pub trait MetricsCollector {
    fn record_timing(&self, operation: &str, duration: Duration);
    fn record_counter(&self, metric: &str, value: u64);
    fn record_gauge(&self, metric: &str, value: f64);
}
```

## Configuration System

```rust
pub struct RepoMapConfig {
    pub token_limit: usize,
    pub model: String,
    pub ignore_patterns: Vec<String>,
    pub export_format: ExportFormat,
    pub analysis_depth: AnalysisDepth,
    pub cache_settings: CacheSettings,
}

pub enum AnalysisDepth {
    Basic,
    Standard,
    Deep,
    Custom(AnalysisSettings),
}

pub struct AnalysisSettings {
    pub semantic_analysis: bool,
    pub pattern_detection: bool,
    pub complexity_analysis: bool,
    pub git_integration: bool,
}
```

## Error Handling

```rust
#[derive(Debug, Error)]
pub enum RepoMapError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    
    #[error("Token limit exceeded: {limit} < {required}")]
    TokenLimitExceeded { limit: usize, required: usize },
    
    #[error("Analysis error: {0}")]
    Analysis(String),
    
    #[error("Cache error: {0}")]
    Cache(String),
    
    #[error("VCS error: {0}")]
    Vcs(String),
    
    #[error("Configuration error: {0}")]
    Config(String),
}
```

## Usage Example

```rust
async fn generate_repo_map() -> Result<String, RepoMapError> {
    let config = RepoMapConfig::new()
        .with_model("gpt-4")
        .with_token_limit(8000)
        .with_export_format(ExportFormat::Markdown)
        .with_analysis_depth(AnalysisDepth::Standard);
        
    let repo_map = RepoMap::new(config);
    
    // Analysis phase
    let analysis = repo_map.analyze().await?;
    
    // Tree generation
    let tree = repo_map.generate_tree(analysis).await?;
    
    // Export
    repo_map.export(tree).await
}
```

## Testing Strategy

1. Unit Tests
```rust
#[cfg(test)]
mod tests {
    #[test]
    fn test_token_counting() {
        let manager = TokenManager::new("gpt-4");
        assert_eq!(manager.count_tokens("Hello, World!"), 3);
    }
    
    #[test]
    fn test_tree_generation() {
        let builder = TreeBuilder::new();
        let tree = builder.build(&test_config()).unwrap();
        assert_eq!(tree.nodes.len(), 2);
    }
}
```

2. Integration Tests
```rust
#[cfg(test)]
mod integration_tests {
    #[tokio::test]
    async fn test_full_analysis() {
        let repo_map = RepoMap::new(test_config());
        let result = repo_map.analyze().await.unwrap();
        assert!(result.contains("src"));
    }
}
```

3. Benchmarks
```rust
#[cfg(test)]
mod benchmarks {
    use criterion::{criterion_group, criterion_main, Criterion};
    
    fn benchmark_analysis(c: &mut Criterion) {
        c.bench_function("analyze repo", |b| {
            b.iter(|| {
                let repo_map = RepoMap::new(test_config());
                repo_map.analyze()
            })
        });
    }
}
```

## Next Steps

1. Initial Setup
   - Create crate structure
   - Set up CI/CD pipeline
   - Configure test environment

2. Core Implementation
   - Implement TokenManager
   - Create basic file system abstraction
   - Set up tree generation system

3. Testing
   - Write core unit tests
   - Set up integration test infrastructure
   - Create benchmark suite

4. Documentation
   - API documentation
   - Usage examples
   - Architecture overview