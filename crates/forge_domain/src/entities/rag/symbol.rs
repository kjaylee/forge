use std::path::PathBuf;
use serde::{Serialize, Deserialize};
use schemars::JsonSchema;

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum SymbolQuery {
    Id(SymbolId),
    Name(String),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize, JsonSchema)]
pub struct SymbolId(pub String);

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize, JsonSchema)]
pub struct Symbol {
    pub id: SymbolId,
    pub name: String,
    pub kind: SymbolKind,
    pub location: Location,
    pub workspace_path: PathBuf,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize, JsonSchema)]
pub struct Location {
    pub path: PathBuf,
    pub start: usize,
    pub end: usize,
}

#[derive(Clone, Debug, Eq, PartialEq, Copy, Serialize, Deserialize, JsonSchema)]
pub enum SymbolKind {
    Function,
    Class,
    Interface,
    Variable,
    Module,
    Namespace,
    Implementation,
    Struct,
    Method,
    Constructor,
    Package,
    Field,
    Property,
    Enum,
    EnumMember,
    Constant,
    Trait,
}

#[derive(Clone, Debug, Eq, PartialEq, Copy, Serialize, Deserialize, JsonSchema)]
pub enum RelationshipKind {
    Calls,
    Implements,
    Inherits,
    Uses,
    Contains,
    References,
    ImportsFrom,
    ExportsTo,
}

impl std::fmt::Display for RelationshipKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RelationshipKind::Calls => write!(f, "calls"),
            RelationshipKind::Implements => write!(f, "implements"),
            RelationshipKind::Inherits => write!(f, "inherits"),
            RelationshipKind::Uses => write!(f, "uses"),
            RelationshipKind::Contains => write!(f, "contains"),
            RelationshipKind::References => write!(f, "references"),
            RelationshipKind::ImportsFrom => write!(f, "imports_from"),
            RelationshipKind::ExportsTo => write!(f, "exports_to"),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct SymbolRelationship {
    pub from: SymbolId,
    pub to: SymbolId,
    pub kind: RelationshipKind,
}

impl SymbolRelationship {
    pub fn new(from: SymbolId, to: SymbolId, kind: RelationshipKind) -> Self {
        Self { from, to, kind }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct CodeContext {
    pub symbols: Vec<Symbol>,
    pub relationships: Vec<SymbolRelationship>,
    pub workspace_root: PathBuf,
}

impl CodeContext {
    pub fn new(
        symbols: Vec<Symbol>,
        relationships: Vec<SymbolRelationship>,
        workspace_root: PathBuf,
    ) -> Self {
        Self {
            symbols,
            relationships,
            workspace_root,
        }
    }

    pub fn empty(workspace_root: PathBuf) -> Self {
        Self {
            symbols: Vec::new(),
            relationships: Vec::new(),
            workspace_root,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_relationship_kind_display() {
        assert_eq!(RelationshipKind::Calls.to_string(), "calls");
        assert_eq!(RelationshipKind::Implements.to_string(), "implements");
        assert_eq!(RelationshipKind::Inherits.to_string(), "inherits");
        assert_eq!(RelationshipKind::Uses.to_string(), "uses");
        assert_eq!(RelationshipKind::Contains.to_string(), "contains");
        assert_eq!(RelationshipKind::References.to_string(), "references");
        assert_eq!(RelationshipKind::ImportsFrom.to_string(), "imports_from");
        assert_eq!(RelationshipKind::ExportsTo.to_string(), "exports_to");
    }

    #[test]
    fn test_symbol_relationship_new() {
        let from = SymbolId("from".to_string());
        let to = SymbolId("to".to_string());
        let kind = RelationshipKind::Calls;

        let relationship = SymbolRelationship::new(from.clone(), to.clone(), kind);

        assert_eq!(relationship.from, from);
        assert_eq!(relationship.to, to);
        assert_eq!(relationship.kind, kind);
    }

    #[test]
    fn test_code_context_empty() {
        let workspace_root = PathBuf::from("/test/path");
        let context = CodeContext::empty(workspace_root.clone());

        assert!(context.symbols.is_empty());
        assert!(context.relationships.is_empty());
        assert_eq!(context.workspace_root, workspace_root);
    }

    #[test]
    fn test_code_context_new() {
        let workspace_root = PathBuf::from("/test/path");
        let symbol = Symbol {
            id: SymbolId("test".to_string()),
            name: "test".to_string(),
            kind: SymbolKind::Function,
            location: Location {
                path: "test.rs".into(),
                start: 0,
                end: 0,
            },
            workspace_path: "test".into(),
        };
        let relationship = SymbolRelationship::new(
            SymbolId("from".to_string()),
            SymbolId("to".to_string()),
            RelationshipKind::Calls,
        );

        let context = CodeContext::new(
            vec![symbol.clone()],
            vec![relationship.clone()],
            workspace_root.clone(),
        );

        assert_eq!(context.symbols.len(), 1);
        assert_eq!(context.symbols[0].id, symbol.id);
        assert_eq!(context.relationships.len(), 1);
        assert_eq!(context.relationships[0].from, relationship.from);
        assert_eq!(context.workspace_root, workspace_root);
    }

    #[test]
    fn test_symbol_query_variants() {
        let id_query = SymbolQuery::Id(SymbolId("test".to_string()));
        let name_query = SymbolQuery::Name("test".to_string());

        match id_query {
            SymbolQuery::Id(id) => assert_eq!(id.0, "test"),
            _ => panic!("Expected Id variant"),
        }

        match name_query {
            SymbolQuery::Name(name) => assert_eq!(name, "test"),
            _ => panic!("Expected Name variant"),
        }
    }

    #[test]
    fn test_location_equality() {
        let loc1 = Location {
            path: PathBuf::from("test.rs"),
            start: 0,
            end: 10,
        };
        let loc2 = Location {
            path: PathBuf::from("test.rs"),
            start: 0,
            end: 10,
        };
        let loc3 = Location {
            path: PathBuf::from("other.rs"),
            start: 0,
            end: 10,
        };

        assert_eq!(loc1, loc2);
        assert_ne!(loc1, loc3);
    }

    #[test]
    fn test_hash_location() {
        use std::collections::HashSet;

        let loc1 = Location {
            path: PathBuf::from("test.rs"),
            start: 0,
            end: 10,
        };
        let loc2 = Location {
            path: PathBuf::from("test.rs"),
            start: 0,
            end: 10,
        };
        let loc3 = Location {
            path: PathBuf::from("other.rs"),
            start: 0,
            end: 10,
        };

        let mut set = HashSet::new();
        set.insert(loc1.clone());
        assert!(set.contains(&loc2));
        assert!(!set.contains(&loc3));
    }

    #[test]
    fn test_serde_symbol_query() {
        let query = SymbolQuery::Name("test".to_string());
        let serialized = serde_json::to_string(&query).unwrap();
        let deserialized: SymbolQuery = serde_json::from_str(&serialized).unwrap();

        match deserialized {
            SymbolQuery::Name(name) => assert_eq!(name, "test"),
            _ => panic!("Expected Name variant"),
        }
    }

    #[test]
    fn test_serde_code_context() {
        let workspace_root = PathBuf::from("/test/path");
        let symbol = Symbol {
            id: SymbolId("test".to_string()),
            name: "test".to_string(),
            kind: SymbolKind::Function,
            location: Location {
                path: "test.rs".into(),
                start: 0,
                end: 0,
            },
            workspace_path: "test".into(),
        };
        let relationship = SymbolRelationship::new(
            SymbolId("from".to_string()),
            SymbolId("to".to_string()),
            RelationshipKind::Calls,
        );
        let context = CodeContext::new(
            vec![symbol],
            vec![relationship],
            workspace_root,
        );

        let serialized = serde_json::to_string(&context).unwrap();
        let deserialized: CodeContext = serde_json::from_str(&serialized).unwrap();

        assert_eq!(deserialized.symbols.len(), 1);
        assert_eq!(deserialized.relationships.len(), 1);
    }
}