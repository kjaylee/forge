use std::path::PathBuf;
use serde::{Serialize, Deserialize};
use std::fmt;

/// Represents a location in a source file, including the file path and position information.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Location {
    /// The path to the source file
    pub path: PathBuf,
    /// Starting line number (1-based)
    pub start_line: usize,
    /// Ending line number (1-based)
    pub end_line: usize,
    /// Starting column number (0-based)
    pub start_col: usize,
    /// Ending column number (0-based)
    pub end_col: usize,
}

/// Represents different types of symbols that can be found in source code.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum SymbolKind {
    /// A function definition
    Function,
    /// A method within a class or struct
    Method,
    /// A class definition
    Class,
    /// An interface definition
    Interface,
    /// A struct definition
    Struct,
    /// An enum definition
    Enum,
    /// A constant value
    Constant,
    /// A variable declaration
    Variable,
    /// A module or namespace
    Module,
    /// A trait definition (Rust)
    Trait,
    /// An implementation block (Rust)
    Implementation,
}

impl fmt::Display for SymbolKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SymbolKind::Function => write!(f, "fn"),
            SymbolKind::Method => write!(f, "method"),
            SymbolKind::Class => write!(f, "class"),
            SymbolKind::Interface => write!(f, "interface"),
            SymbolKind::Struct => write!(f, "struct"),
            SymbolKind::Enum => write!(f, "enum"),
            SymbolKind::Constant => write!(f, "const"),
            SymbolKind::Variable => write!(f, "var"),
            SymbolKind::Module => write!(f, "mod"),
            SymbolKind::Trait => write!(f, "trait"),
            SymbolKind::Implementation => write!(f, "impl"),
        }
    }
}

/// Represents a symbol found in the source code, such as a function, class, or variable.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Symbol {
    /// The name of the symbol
    pub name: String,
    /// The kind of symbol (e.g., function, class, etc.)
    pub kind: SymbolKind,
    /// Optional signature for functions and methods
    pub signature: Option<String>,
    /// The location where this symbol is defined
    pub location: Location,
    /// A score indicating the symbol's importance in the codebase (higher is more important)
    pub importance: f64,
    /// Locations where this symbol is referenced
    pub references: Vec<Location>,
}

impl Symbol {
    pub fn new(
        name: String,
        kind: SymbolKind,
        location: Location,
    ) -> Self {
        Self {
            name,
            kind,
            signature: None,
            location,
            importance: 1.0,
            references: Vec::new(),
        }
    }

    pub fn with_signature(mut self, signature: String) -> Self {
        self.signature = Some(signature);
        self
    }

    pub fn add_reference(&mut self, reference: Location) {
        self.references.push(reference);
        self.recalculate_importance();
    }

    fn recalculate_importance(&mut self) {
        // Basic importance calculation based on number of references
        self.importance = 1.0 + (self.references.len() as f64 * 0.1);
    }
}