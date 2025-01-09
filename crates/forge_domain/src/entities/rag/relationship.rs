use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
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

impl fmt::Display for RelationshipKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RelationshipKind::Calls => write!(f, "calls"),
            RelationshipKind::Implements => write!(f, "implements"),
            RelationshipKind::Inherits => write!(f, "inherits"),
            RelationshipKind::Uses => write!(f, "uses"),
            RelationshipKind::Contains => write!(f, "contains"),
            RelationshipKind::References => write!(f, "references"),
            RelationshipKind::ImportsFrom => write!(f, "imports from"),
            RelationshipKind::ExportsTo => write!(f, "exports to"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolRelationship {
    pub from: super::SymbolId,
    pub to: super::SymbolId,
    pub kind: RelationshipKind,
}

impl SymbolRelationship {
    pub fn new(from: super::SymbolId, to: super::SymbolId, kind: RelationshipKind) -> Self {
        Self { from, to, kind }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::SymbolId;
    
    #[test]
    fn test_relationship_kind_display() {
        assert_eq!(RelationshipKind::Calls.to_string(), "calls");
        assert_eq!(RelationshipKind::Implements.to_string(), "implements");
        assert_eq!(RelationshipKind::Inherits.to_string(), "inherits");
        assert_eq!(RelationshipKind::Uses.to_string(), "uses");
        assert_eq!(RelationshipKind::Contains.to_string(), "contains");
        assert_eq!(RelationshipKind::References.to_string(), "references");
        assert_eq!(RelationshipKind::ImportsFrom.to_string(), "imports from");
        assert_eq!(RelationshipKind::ExportsTo.to_string(), "exports to");
    }

    #[test]
    fn test_relationship_creation() {
        let from = SymbolId("test1".to_string());
        let to = SymbolId("test2".to_string());
        let kind = RelationshipKind::Calls;

        let relationship = SymbolRelationship::new(from.clone(), to.clone(), kind.clone());

        assert_eq!(relationship.from, from);
        assert_eq!(relationship.to, to);
        assert_eq!(relationship.kind, kind);
    }
}