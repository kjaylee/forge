use std::fmt::Display;
use std::path::PathBuf;

/// Represents the type of code block captured
#[derive(Debug, Clone, PartialEq)]
pub enum Kind {
    Function,
    Struct,
    Enum,
    Constant,
}

impl Display for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Kind::Function => write!(f, "function"),
            Kind::Struct => write!(f, "struct"),
            Kind::Enum => write!(f, "enum"),
            Kind::Constant => write!(f, "constant"),
        }
    }
}

/// Represents a specific scope for the code block
#[derive(Debug, Clone, PartialEq)]
pub enum Scope {
    Test,
}

impl Display for Scope {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Scope::Test => write!(f, "test"),
        }
    }
}

/// Represents a captured code block with metadata
#[derive(Debug, Clone, PartialEq)]
pub struct Block {
    /// what type of snippet captured
    pub kind: Kind,
    /// code file path
    pub path: PathBuf,
    /// code snippet
    pub snippet: String,
    /// scope of kind
    pub scope: Option<Scope>,
    /// Span of snippet
    pub span: Span,
    /// Char offset of snippet
    pub offset: Offset,
}

impl Block {
    pub fn hash(&self) -> String {
        use blake3::Hasher as Blake3;
        let mut hasher = Blake3::new();
        hasher.update(self.path.display().to_string().as_bytes());
        hasher.update(self.snippet.as_bytes());
        let hash = hasher.finalize();
        hash.to_hex().to_string()
    }

    pub fn relative_path(&self) -> PathBuf {
        let current_dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        pathdiff::diff_paths(&self.path, &current_dir).unwrap_or_else(|| self.path.clone())
    }
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct Offset {
    pub start: usize,
    pub end: usize,
}

impl Block {
    /// Create a new code block
    pub fn new(
        kind: Kind,
        path: PathBuf,
        snippet: String,
        scope: Option<Scope>,
        span: Span,
        offset: Offset,
    ) -> Self {
        Self { kind, path, snippet, scope, span, offset }
    }
}

/// Represents a source code span with start and end locations
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct Span {
    pub start: Location,
    pub end: Location,
}

/// Represents a location in source code with line and column
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct Location {
    pub line: usize,
    pub column: usize,
}

impl From<tree_sitter::Point> for Location {
    fn from(point: tree_sitter::Point) -> Self {
        Self { line: point.row, column: point.column }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_relative_path() {
        let block = Block::new(
            Kind::Function,
            PathBuf::from(
                "/Users/ranjit/Desktop/workspace/code-forge/code-forge/crates/forge_main/src/prompt.rs",
            ),
            "fn main() -> ()".to_string(),
            None,
            Span {
                start: Location { line: 0, column: 0 },
                end: Location { line: 0, column: 0 },
            },
            Offset { start: 0, end: 0 },
        );

        println!("path: {}", block.relative_path().display());
    }
}
