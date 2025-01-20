use std::fmt;
use std::path::PathBuf;
use std::rc::Rc;

use serde::{Deserialize, Serialize};

/// Represents a location in a source file, including the file path and position
/// information.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Location {
    /// The path to the source file
    pub path: Rc<PathBuf>,
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

impl SymbolKind {
    /// Get the base weight for this symbol kind for importance calculations
    pub fn base_weight(&self) -> f64 {
        match self {
            SymbolKind::Module => 1.5,         // Highest weight for modules
            SymbolKind::Trait => 1.4,          // Traits are important for Rust
            SymbolKind::Interface => 1.4,      // Interfaces are important
            SymbolKind::Class => 1.3,          // Classes define major structures
            SymbolKind::Struct => 1.3,         // Structs are like classes
            SymbolKind::Enum => 1.2,           // Enums define important types
            SymbolKind::Function => 1.1,       // Functions are common but important
            SymbolKind::Method => 1.1,         // Methods are like functions
            SymbolKind::Implementation => 1.1, // Implementations are important
            SymbolKind::Constant => 0.9,       // Constants are referenced but simple
            SymbolKind::Variable => 0.8,       // Variables have lowest weight
        }
    }
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

/// Represents a symbol found in the source code, such as a function, class, or
/// variable.
#[derive(Debug, Clone)]
pub struct Symbol {
    /// The name of the symbol
    pub name: Rc<String>,
    /// The kind of symbol (e.g., function, class, etc.)
    pub kind: SymbolKind,
    /// Optional signature for functions and methods
    pub signature: Option<Rc<String>>,
    /// The location where this symbol is defined
    pub location: Location,
    /// A score indicating the symbol's importance in the codebase (higher is
    /// more important)
    pub importance: f64,
    /// Locations where this symbol is referenced
    pub references: Vec<Location>,
}

impl Symbol {
    pub fn new(name: String, kind: SymbolKind, location: Location) -> Self {
        let base_weight = kind.base_weight();
        Self {
            name: Rc::new(name),
            kind,
            signature: None,
            location,
            importance: base_weight,
            references: Vec::new(),
        }
    }

    pub fn with_signature(mut self, signature: String) -> Self {
        let signature_bonus = 0.1;
        self.signature = Some(Rc::new(signature));
        self.importance += signature_bonus;
        self
    }

    pub fn add_reference(&mut self, reference: Location) {
        self.references.push(reference);
        self.recalculate_importance();
    }

    fn recalculate_importance(&mut self) {
        // Improved importance calculation
        // - Uses base weight of the symbol type
        // - Logarithmic scaling for number of references
        // - Small bonus for having a signature
        let reference_multiplier = 1.0 + (self.references.len() as f64).ln().max(0.0) * 0.2;
        let signature_bonus = if self.signature.is_some() { 0.1 } else { 0.0 };

        self.importance = self.kind.base_weight() * reference_multiplier + signature_bonus;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_symbol_weights() {
        assert!(SymbolKind::Module.base_weight() > SymbolKind::Variable.base_weight());
        assert!(SymbolKind::Class.base_weight() > SymbolKind::Constant.base_weight());
        assert_eq!(
            SymbolKind::Function.base_weight(),
            SymbolKind::Method.base_weight()
        );
    }

    #[test]
    fn test_importance_calculation() {
        let location = Location {
            path: Rc::new(PathBuf::from("test.rs")),
            start_line: 1,
            end_line: 1,
            start_col: 0,
            end_col: 0,
        };

        let mut symbol = Symbol::new("test".to_string(), SymbolKind::Function, location.clone());

        let initial_importance = symbol.importance;

        // Add some references
        for _ in 0..5 {
            symbol.add_reference(location.clone());
        }

        assert!(symbol.importance > initial_importance);
    }

    #[test]
    fn test_symbol_with_signature() {
        let location = Location {
            path: Rc::new(PathBuf::from("test.rs")),
            start_line: 1,
            end_line: 1,
            start_col: 0,
            end_col: 0,
        };

        let base_symbol = Symbol::new("test".to_string(), SymbolKind::Function, location);

        let base_importance = base_symbol.importance;

        let symbol_with_sig = base_symbol.with_signature("fn test(x: i32) -> i32".to_string());

        assert!(symbol_with_sig.importance > base_importance,
            "Symbol with signature (importance: {}) should have higher importance than base symbol (importance: {})",
            symbol_with_sig.importance,
            base_importance
        );
    }
}
