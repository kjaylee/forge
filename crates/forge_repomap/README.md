# forge_repomap

A Rust library for building comprehensive maps of code repositories to provide context for LLMs. Inspired by [Aider's repository map](https://aider.chat/docs/repomap.html), this library helps understand code structure, dependencies, and relationships within a codebase.

## Features

- **Symbol Extraction**: Identifies functions, classes, methods, and other code elements
- **Dependency Tracking**: Maps relationships between files and symbols
- **Smart Context**: Generates LLM-friendly context optimized for token limits
- **Multi-Language Support**: Works with:
  - Rust
  - JavaScript
  - Python
  - TypeScript
- **Token Budget Management**: Efficiently manages context size for LLM interactions

## Installation

Add this to your `Cargo.toml`:

```toml
[dependencies]
forge_repomap = { path = "../forge_repomap" }
```

## Quick Start

```rust
use std::path::PathBuf;
use forge_repomap::RepoMap;

// Create a new repo map with a token budget
let mut repo_map = RepoMap::new(
    PathBuf::from("./"), // Repository root path
    1000,               // Token budget for context
)?;

// Analyze the repository
repo_map.analyze()?;

// Get context about specific files
let context = repo_map.get_context(&[
    PathBuf::from("src/main.rs"),
    PathBuf::from("src/lib.rs"),
]);
```

## How It Works

### 1. Repository Analysis

The RepoMap analyzes your repository in several stages:

1. **File Discovery**: Traverses the repository to find source files
2. **Symbol Extraction**: Uses tree-sitter to parse files and extract symbols
3. **Dependency Analysis**: Builds a graph of file and symbol relationships
4. **Importance Scoring**: Ranks code elements by their significance

### 2. Context Generation

When providing context to LLMs, RepoMap:

1. Prioritizes directly relevant files
2. Includes important related symbols
3. Optimizes output for the token budget
4. Formats context in a clear, LLM-friendly way

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

### 3. Symbol Types

RepoMap tracks various types of code symbols:

- Functions and Methods
- Classes and Structs
- Interfaces and Traits
- Variables and Constants
- Modules and Namespaces

## Advanced Usage

### Custom Token Budgets

Adjust context size based on your LLM's requirements:

```rust
// More context for GPT-4
let mut large_map = RepoMap::new(root_path, 2000)?;

// Less context for smaller models
let mut small_map = RepoMap::new(root_path, 500)?;
```

### Focus on Specific Files

Get context about particular files and their dependencies:

```rust
let context = repo_map.get_context(&[
    PathBuf::from("src/important_module.rs"),
    PathBuf::from("src/related_code.rs"),
]);
```

### File Updates

Update the map when files change:

```rust
repo_map.update_file(PathBuf::from("src/modified_file.rs"))?;
```

## Architecture

RepoMap consists of several key components:

- **Parser**: Uses tree-sitter for accurate code analysis
- **DependencyGraph**: Tracks relationships between files
- **SymbolExtractor**: Identifies and categorizes code elements
- **TokenBudget**: Manages context size optimization

## Error Handling

RepoMap provides detailed error information:

```rust
use forge_repomap::Error;

match repo_map.analyze() {
    Ok(_) => println!("Analysis complete"),
    Err(Error::UnsupportedLanguage(lang)) => {
        eprintln!("Unsupported language: {}", lang)
    }
    Err(Error::Parse(msg)) => {
        eprintln!("Parse error: {}", msg)
    }
    Err(e) => eprintln!("Error: {}", e),
}
```

## Contributing

Key areas for contribution:

1. Additional language support
2. Performance optimizations
3. Enhanced symbol detection
4. Improved importance scoring algorithms

## License

This project is part of the Code Forge workspace.

## Acknowledgments

- Inspired by [Aider's repository map](https://aider.chat/docs/repomap.html)
- Uses [Tree-sitter](https://tree-sitter.github.io/) for code parsing
- Built with Rust 🦀