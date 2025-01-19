use std::path::PathBuf;
use serde::{Serialize, Deserialize};
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Location {
    pub path: PathBuf,
    pub start_line: usize,
    pub end_line: usize,
    pub start_col: usize,
    pub end_col: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum SymbolKind {
    Function,
    Method,
    Class,
    Interface,
    Struct,
    Enum,
    Constant,
    Variable,
    Module,
    Trait,
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

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Symbol {
    pub name: String,
    pub kind: SymbolKind,
    pub signature: Option<String>,
    pub location: Location,
    pub importance: f64,
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