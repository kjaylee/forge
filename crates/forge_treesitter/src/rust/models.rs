use std::path::PathBuf;

/// Represents the type of code block captured
#[derive(Debug, Clone, PartialEq)]
pub enum Kind {
    Function,
    Struct,
    Enum,
    Constant,
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
    /// Char offset of snippet
    offset: Offset,
}

#[derive(Debug, Clone, PartialEq)]
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
        offset: Offset
    ) -> Self {
        Self {
            kind,
            path,
            snippet,
            scope,
            span,
            offset
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