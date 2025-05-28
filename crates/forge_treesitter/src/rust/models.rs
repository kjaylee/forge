use std::path::PathBuf;

/// Represents the type of code block captured
#[derive(Debug, Clone, PartialEq)]
pub enum Kind {
    Function,
    Method,
    Struct,
    Enum,
    Impl,
    Trait,
    Constant,
    //... and so on
}

/// Represents a specific scope for the code block
#[derive(Debug, Clone, PartialEq)]
pub enum Scope {
    Test,
}

/// Represents a captured code block with metadata
#[derive(Debug, Clone, PartialEq)]
pub struct Block {
    /// what type of snippet captured
    kind: Kind,
    /// code file path
    path: PathBuf,
    /// code snippet
    snippet: String,
    /// scope of kind
    scope: Option<Scope>,
    /// Span of snippet
    span: Span,
}

impl Block {
    /// Create a new code block
    pub fn new(
        kind: Kind,
        path: PathBuf,
        snippet: String,
        scope: Option<Scope>,
        span: Span,
    ) -> Self {
        Self {
            kind,
            path,
            snippet,
            scope,
            span,
        }
    }
}

/// Represents a source code span with start and end locations
#[derive(Debug, Clone, PartialEq)]
pub struct Span {
    pub start: Location,
    pub end: Location,
}

/// Represents a location in source code with line and column
#[derive(Debug, Clone, PartialEq)]
pub struct Location {
    pub line: usize,
    pub column: usize,
}

impl From<tree_sitter::Point> for Location {
    fn from(point: tree_sitter::Point) -> Self {
        Self { line: point.row, column: point.column }
    }
}