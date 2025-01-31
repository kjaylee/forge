use std::fmt;
use std::path::PathBuf;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct Location {
    pub path: Rc<PathBuf>,
    pub start_line: usize,
    pub end_line: usize,
    pub start_col: usize,
    pub end_col: usize,
}

#[derive(Debug, Clone)]
pub struct SymbolReference {
    pub name: String,
    pub location: Location,
    pub kind: SymbolKind,
    pub is_public: bool,
    pub has_docs: bool,
}

impl SymbolReference {
    pub fn new(name: String, location: Location, kind: SymbolKind) -> Self {
        Self { name, location, kind, is_public: false, has_docs: false }
    }

    pub fn with_visibility(mut self, is_public: bool) -> Self {
        self.is_public = is_public;
        self
    }

    pub fn with_docs(mut self, has_docs: bool) -> Self {
        self.has_docs = has_docs;
        self
    }

    pub fn base_weight(&self) -> f64 {
        self.kind.base_weight()
    }

    pub fn importance_factor(&self) -> f64 {
        let mut factor = self.base_weight();
        if self.is_public {
            factor *= 1.5;
        }
        if self.has_docs {
            factor *= 1.2;
        }
        factor
    }
}

#[derive(Debug, Clone)]
pub struct Symbol {
    pub name: String,
    pub kind: SymbolKind,
    pub scope: Option<Scope>,
    pub references: Vec<SymbolReference>,
    pub signature: Option<String>,
    pub location: Location,
}

impl Symbol {
    pub fn new(name: String, kind: SymbolKind, location: Location) -> Self {
        Self {
            name,
            kind,
            scope: None,
            references: Vec::new(),
            signature: None,
            location,
        }
    }

    pub fn with_scope(mut self, scope: Scope) -> Self {
        self.scope = Some(scope);
        self
    }

    pub fn with_signature(mut self, signature: String) -> Self {
        self.signature = Some(signature);
        self
    }

    pub fn add_reference(&mut self, reference: SymbolReference) {
        self.references.push(reference);
    }

    pub fn is_public(&self) -> bool {
        // A symbol is public if it has public visibility in its references
        self.references.iter().any(|r| r.is_public)
    }

    pub fn has_docs(&self) -> bool {
        // A symbol has docs if any of its references has docs
        self.references.iter().any(|r| r.has_docs)
    }

    pub fn importance_factor(&self) -> f64 {
        let mut factor = self.kind.base_weight();
        if self.is_public() {
            factor *= 1.5;
        }
        if self.has_docs() {
            factor *= 1.2;
        }
        factor
    }
}

#[derive(Debug, Clone, PartialEq)]
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
    TypeAlias,
    Macro,
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
            SymbolKind::TypeAlias => write!(f, "type"),
            SymbolKind::Macro => write!(f, "macro"),
        }
    }
}

impl SymbolKind {
    pub fn base_weight(&self) -> f64 {
        match self {
            SymbolKind::Function | SymbolKind::Method => 1.0,
            SymbolKind::Class | SymbolKind::Interface => 1.5,
            SymbolKind::Struct | SymbolKind::Trait => 1.3,
            SymbolKind::Enum => 0.8,
            SymbolKind::Constant => 0.5,
            SymbolKind::Variable => 0.3,
            SymbolKind::Module => 2.0,
            SymbolKind::TypeAlias => 0.7,
            SymbolKind::Macro => 1.2,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ScopeType {
    Module,
    Function,
    Block,
    Class,
    Interface,
    None,
}

#[derive(Debug, Clone)]
pub struct Scope {
    pub scope_type: ScopeType,
    pub start_line: usize,
    pub end_line: usize,
    pub parent_scope: Option<Box<Scope>>,
}

impl Scope {
    pub fn new(scope_type: ScopeType, start_line: usize, end_line: usize) -> Self {
        Self { scope_type, start_line, end_line, parent_scope: None }
    }

    pub fn with_parent(mut self, parent: Scope) -> Self {
        self.parent_scope = Some(Box::new(parent));
        self
    }

    pub fn contains_line(&self, line: usize) -> bool {
        line >= self.start_line && line <= self.end_line
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scope_contains_line() {
        let scope = Scope::new(ScopeType::Function, 1, 10);
        assert!(scope.contains_line(5));
        assert!(!scope.contains_line(11));
    }

    #[test]
    fn test_scope_with_parent() {
        let parent = Scope::new(ScopeType::Module, 1, 20);
        let child = Scope::new(ScopeType::Function, 5, 10).with_parent(parent);

        assert!(child.contains_line(7));
        assert!(child.parent_scope.unwrap().contains_line(15));
    }

    #[test]
    fn test_symbol_weights() {
        assert!(
            SymbolKind::Module.base_weight() > SymbolKind::Function.base_weight(),
            "Modules should have higher base weight than functions"
        );
        assert!(
            SymbolKind::Class.base_weight() > SymbolKind::Variable.base_weight(),
            "Classes should have higher base weight than variables"
        );
    }

    #[test]
    fn test_symbol_metadata() {
        let path = Rc::new(PathBuf::from("test.rs"));
        let location = Location {
            path: Rc::clone(&path),
            start_line: 1,
            end_line: 1,
            start_col: 0,
            end_col: 0,
        };

        let mut symbol = Symbol::new("test".to_string(), SymbolKind::Function, location.clone())
            .with_signature("fn test() -> ()".to_string());

        // Add a public reference
        symbol.add_reference(
            SymbolReference::new("test".to_string(), location.clone(), SymbolKind::Function)
                .with_visibility(true)
                .with_docs(true),
        );

        assert_eq!(symbol.signature.as_ref().unwrap(), "fn test() -> ()");
        assert!(symbol.is_public(), "Symbol should be public");
        assert!(symbol.has_docs(), "Symbol should have docs");
        assert!(
            symbol.importance_factor() > symbol.kind.base_weight(),
            "Importance factor should be higher than base weight"
        );
    }
}
