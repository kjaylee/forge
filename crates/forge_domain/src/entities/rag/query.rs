use super::symbol::SymbolId;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymbolQuery {
    Id(SymbolId),
    Name(String),
}