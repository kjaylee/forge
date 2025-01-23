use std::collections::HashMap;
use tree_sitter::{Language, Node, Query, QueryCursor};
use streaming_iterator::StreamingIterator;
use crate::error::{LanguageError, Result};
use crate::language::LanguageSyntaxConfig;
use crate::parser::ParsedSource;

pub struct QueryEngine {
    cache: HashMap<String, tree_sitter::Query>,
    language: Language,
}

#[derive(Debug)]
pub struct QueryMatch<'a> {
    pub pattern_index: usize,
    pub captures: Vec<QueryCapture<'a>>,
}

#[derive(Debug)]
pub struct QueryCapture<'a> {
    pub name: String,
    pub node: Node<'a>,
    pub index: u32,
}

impl QueryEngine {
    /// Create a new QueryEngine from a Language
    pub fn new(language: Language) -> Self {
        Self {
            cache: HashMap::new(),
            language,
        }
    }

    /// Create a new QueryEngine from a LanguageSyntaxConfig
    pub fn from_config(config: &'static LanguageSyntaxConfig) -> Result<Self> {
        Ok(Self::new(config.grammar.clone()))
    }

    /// Execute a query against a ParsedSource
    pub fn query<'tree>(
        &mut self,
        query_source: &str,
        parsed: &'tree ParsedSource,
    ) -> Result<Vec<QueryMatch<'tree>>> {
        self.execute(query_source, parsed.tree().root_node(), parsed.source())
    }

    /// Execute a query against a specific node and source bytes
    pub fn execute<'tree>(
        &mut self,
        query_source: &str,
        node: Node<'tree>,
        source: &'tree [u8],
    ) -> Result<Vec<QueryMatch<'tree>>> {
        let compiled = self.get_or_compile_query(query_source)?;
        let mut cursor = QueryCursor::new();
        let mut matches = Vec::new();
        
        // Get matches using cursor.matches and streaming iterator
        let mut query_matches = cursor.matches(compiled, node, source);
        
        while let Some(m) = query_matches.next() {
            // Get current match
            matches.push(QueryMatch {
                pattern_index: m.pattern_index,
                captures: m.captures
                    .iter()
                    .map(|c| QueryCapture {
                        name: compiled.capture_names()[c.index as usize].to_string(),
                        node: c.node,
                        index: c.index,
                    })
                    .collect(),
            });
        }
            
        Ok(matches)
    }

    fn get_or_compile_query(&mut self, query_source: &str) -> Result<&Query> {
        if !self.cache.contains_key(query_source) {
            let compiled = Query::new(&self.language, query_source)
                .map_err(|e| LanguageError::QueryError(e.to_string()))?;
            self.cache.insert(query_source.to_string(), compiled);
        }
        Ok(&self.cache[query_source])
    }
}
