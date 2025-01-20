# forge_repomap

A Rust library for building comprehensive maps of code repositories to provide context for LLMs. Inspired by [Aider's repository map](https://aider.chat/docs/repomap.html), this library helps understand code structure, dependencies, and relationships within a codebase.

## Features

### Core Features
- **Smart Symbol Analysis**: Identifies and ranks code elements based on their type and usage
- **PageRank-Based Importance**: Uses a modified PageRank algorithm for context relevance
- **Precise Token Estimation**: Code-aware token counting for accurate LLM context management
- **Type-Safe Implementation**: Strong compile-time guarantees and Rust's type system benefits

### Symbol Hierarchy
Automatically weights different types of symbols:
- Modules (1.5x) - Highest importance for structural elements
- Traits/Interfaces (1.4x) - Core abstractions
- Classes/Structs (1.3x) - Major data structures
- Enums (1.2x) - Type definitions
- Functions/Methods (1.1x) - Behavioral elements
- Constants (0.9x) - Named values
- Variables (0.8x) - Basic elements

### Language Support
Currently supports:
- Rust (.rs)
- JavaScript (.js)
- Python (.py)
- TypeScript (.ts, .tsx)

## Installation

Add this to your `Cargo.toml`:

```toml
[dependencies]
forge_repomap = { path = "../forge_repomap" }
```

## Quick Start

```rust
use std::path::PathBuf;
use forge_repomap::{RepoMap, PageRankConfig, SourceFile};

// Create a new repo map
let mut repo_map = RepoMap::new(PathBuf::from("./"), 1000)?
    .with_parser()?
    .with_page_rank_config(PageRankConfig {
        damping_factor: 0.85,
        max_iterations: 100,
        tolerance: 1e-6,
    });

// Process source files
let sources = vec![
    SourceFile {
        path: PathBuf::from("src/main.rs"),
        content: std::fs::read_to_string("src/main.rs")?,
    },
    SourceFile {
        path: PathBuf::from("src/lib.rs"),
        content: std::fs::read_to_string("src/lib.rs")?,
    },
];

// Process all files
repo_map.process_files(sources)?;

// Get context about specific files
let context = repo_map.get_context(&[
    PathBuf::from("src/main.rs"),
    PathBuf::from("src/lib.rs"),
])?;
```

## How It Works

### 1. Symbol Analysis and Ranking

#### Symbol Extraction
- Parses code using tree-sitter
- Identifies symbols and their relationships
- Tracks references and dependencies

#### Importance Calculation
Uses a sophisticated ranking system:
1. **Base Weights**: Different weights for different symbol types
2. **Reference Impact**: Logarithmic scaling of reference counts
3. **Signature Bonus**: Additional weight for well-documented symbols
4. **PageRank Integration**: Modified PageRank algorithm for global importance

### 2. Context Generation

The context generation process:

1. **Focus Prioritization**: 
   - Directly referenced files get highest priority
   - Uses PageRank with personalization for focus files

2. **Smart Token Management**:
   - Code-aware token estimation
   - Handles special programming patterns
   - Accounts for structure and syntax

Example context output:
```text
src/main.rs:
│fn main() -> Result<()>
│struct Config
│----impl Config

src/lib.rs:
│trait Repository<T>
│struct UserRepository
│----impl Repository<User> for UserRepository
```

### 3. Dependency Graph

- Tracks file and symbol relationships
- Weighted edges based on symbol importance
- Reference counting and relationship strength
- PageRank-based importance propagation

## Advanced Usage

### Custom PageRank Configuration

Fine-tune the importance calculation:

```rust
use forge_repomap::PageRankConfig;

let config = PageRankConfig {
    damping_factor: 0.85,  // Balance between global and local importance
    max_iterations: 100,   // Maximum convergence attempts
    tolerance: 1e-6,       // Convergence threshold
};

let repo_map = RepoMap::new(root_path, token_budget)?
    .with_page_rank_config(config);
```

### Process Individual Files

Process files one at a time:

```rust
let source = SourceFile {
    path: PathBuf::from("src/important.rs"),
    content: String::from("// Source code content here"),
};

repo_map.process_file(source)?;
```

### Batch Processing

Process multiple files at once:

```rust
let sources = vec![
    SourceFile {
        path: PathBuf::from("src/file1.rs"),
        content: String::from("// Content 1"),
    },
    SourceFile {
        path: PathBuf::from("src/file2.rs"),
        content: String::from("// Content 2"),
    },
];

repo_map.process_files(sources)?;
```

### Focus-Based Context

Get context with emphasis on specific files:

```rust
// Files in the Vec get higher importance in the context
let context = repo_map.get_context(&[
    PathBuf::from("src/important.rs"),
    PathBuf::from("src/related.rs"),
])?;
```

## Architecture

### Core Components

1. **Symbol System**
   - Hierarchical symbol types
   - Reference tracking
   - Importance calculation

2. **Ranking System**
   - PageRank-based algorithm
   - Symbol weight integration
   - Focus file personalization

3. **Token Management**
   - Code-aware estimation
   - Pattern recognition
   - Structure awareness

### Technical Details

- **Graph Implementation**: Uses `petgraph` for dependency tracking
- **Parser**: Tree-sitter integration for accurate parsing
- **Memory Efficiency**: Smart ownership and reference management
- **Error Handling**: Comprehensive error types and handling

## Error Handling

```rust
use forge_repomap::Error;

match repo_map.process_files(sources) {
    Ok(_) => println!("Processing complete"),
    Err(Error::UnsupportedLanguage(lang)) => {
        eprintln!("Unsupported language: {}", lang)
    }
    Err(Error::Parse(msg)) => {
        eprintln!("Parse error: {}", msg)
    }
    Err(e) => eprintln!("Error: {}", e),
}
```

## Future Improvements

Planned enhancements:
1. Parallel file processing
2. Additional language support
3. Incremental updates
4. Performance optimizations
5. Caching system for parsed symbols

## Contributing

Key areas for contribution:
1. Language support expansion
2. Performance optimization
3. Testing and benchmarks
4. Documentation improvements

## License

This project is part of the Code Forge workspace.

## Acknowledgments

- Inspired by [Aider's repository map](https://aider.chat/docs/repomap.html)
- Uses [Tree-sitter](https://tree-sitter.github.io/) for code parsing
- Built with Rust 🦀