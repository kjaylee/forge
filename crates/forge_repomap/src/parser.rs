use std::collections::HashMap;
use std::path::Path;
use std::sync::Arc;
use std::rc::Rc;
use serde::{Deserialize, Serialize};
use tokio::sync::Semaphore;
use futures::stream::{self, StreamExt};
use tree_sitter::{Language, Parser as TsParser, Query, Node};
use streaming_iterator::StreamingIterator;

use crate::error::Error;
use crate::symbol::{Location, Symbol, Scope, SymbolKind, SymbolReference};
use crate::scope_walker::ScopeWalker;
use crate::ranking::EdgeType;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ReferenceType {
    Use,        // use statements
    Call,       // function calls
    Type,       // type references
    Field,      // field access
    Module,     // module references
    Definition, // symbol definitions
}

impl From<ReferenceType> for EdgeType {
    fn from(rt: ReferenceType) -> Self {
        match rt {
            ReferenceType::Use => EdgeType::Use,
            ReferenceType::Call => EdgeType::Call,
            ReferenceType::Type => EdgeType::Implementation,
            ReferenceType::Field => EdgeType::Use,
            ReferenceType::Module => EdgeType::Import,
            ReferenceType::Definition => EdgeType::Implementation,
        }
    }
}

impl ReferenceType {
    pub fn weight(&self) -> f64 {
        EdgeType::from(*self).base_weight()
    }
}


#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ParseConfig {
    /// Enable parallel parsing of files
    pub parallel_processing: bool,
    /// Maximum number of parallel parsing tasks
    pub max_parallel_tasks: usize,
    /// Enable scope analysis
    pub scope_analysis: bool,
    /// Enable function signature parsing
    pub parse_signatures: bool,
    /// Enable reference tracking
    pub track_references: bool,
}

impl ParseConfig {
    pub fn new() -> Self {
        Self {
            parallel_processing: false,
            max_parallel_tasks: num_cpus::get(),
            scope_analysis: true,
            parse_signatures: true,
            track_references: true,
        }
    }

    pub fn with_parallel_processing(mut self, enabled: bool) -> Self {
        self.parallel_processing = enabled;
        self
    }

    pub fn with_max_parallel_tasks(mut self, max_tasks: usize) -> Self {
        self.max_parallel_tasks = max_tasks;
        self
    }

    pub fn with_scope_analysis(mut self, enabled: bool) -> Self {
        self.scope_analysis = enabled;
        self
    }

    pub fn with_signature_parsing(mut self, enabled: bool) -> Self {
        self.parse_signatures = enabled;
        self
    }

    pub fn with_reference_tracking(mut self, enabled: bool) -> Self {
        self.track_references = enabled;
        self
    }
}

pub struct Parser {
    parsers: HashMap<String, Arc<Language>>,
    queries: HashMap<String, Arc<Query>>,
    config: ParseConfig,
}

impl Parser {
    pub fn new() -> Result<Self, Error> {
        let mut parser = Self {
            parsers: Self::initialize_parsers(),
            queries: HashMap::new(),
            config: ParseConfig::new(),
        };
        
        parser.queries = parser.initialize_queries()?;
        Ok(parser)
    }

    pub fn with_config(mut self, config: ParseConfig) -> Self {
        self.config = config;
        self
    }

    fn initialize_parsers() -> HashMap<String, Arc<Language>> {
        let mut parsers = HashMap::new();
        parsers.insert("rs".to_string(), Arc::new(language_rust()));
        parsers.insert("js".to_string(), Arc::new(language_javascript()));
        parsers.insert("py".to_string(), Arc::new(language_python()));
        parsers.insert("ts".to_string(), Arc::new(language_typescript()));
        parsers.insert("tsx".to_string(), Arc::new(language_typescript()));
        parsers.insert("c".to_string(), Arc::new(language_c()));
        parsers.insert("cpp".to_string(), Arc::new(language_cpp()));
        parsers.insert("hpp".to_string(), Arc::new(language_cpp()));
        parsers.insert("cs".to_string(), Arc::new(language_csharp()));
        parsers.insert("java".to_string(), Arc::new(language_java()));
        parsers.insert("go".to_string(), Arc::new(language_go()));
        parsers.insert("rb".to_string(), Arc::new(language_ruby()));
        parsers.insert("php".to_string(), Arc::new(language_php()));
        parsers
    }

    fn initialize_queries(&self) -> Result<HashMap<String, Arc<Query>>, Error> {
        let mut queries = HashMap::new();

        // Rust query
        Self::load_query(
            &mut queries,
            "rs",
            r#"
            (mod_item
                name: (identifier) @name.definition.module) @scope.definition.module

            (function_item
                name: (identifier) @name.definition.function) @scope.definition.function

            (struct_item
                name: (type_identifier) @name.definition.struct)

            (trait_item
                name: (type_identifier) @name.definition.trait)

            (impl_item) @scope.definition.impl

            (macro_definition
                name: (identifier) @name.definition.macro)

            (type_item
                name: (type_identifier) @name.definition.type)

            (const_item
                name: (identifier) @name.definition.constant)

            ; Scopes
            (mod_item) @scope.module
            (function_item) @scope.function
            (impl_item) @scope.class
            (block) @scope.block

            ; References
            (identifier) @name.reference.identifier
            (type_identifier) @name.reference.type
            "#,
            &tree_sitter_rust::LANGUAGE.into(),
        )?;

        Ok(queries)
    }

    fn load_query(
        queries: &mut HashMap<String, Arc<Query>>,
        language: &str,
        query_source: &str,
        lang: &Language,
    ) -> Result<(), Error> {
        let query = Query::new(lang, query_source)
            .map_err(|e| Error::Parse(format!("Failed to parse {} query: {}", language, e)))?;
        queries.insert(language.to_string(), Arc::new(query));
        Ok(())
    }

    pub async fn parse_files<P: AsRef<Path> + Send + 'static>(
        &self,
        files: Vec<(P, String)>,
    ) -> Result<HashMap<P, Vec<Symbol>>, Error>
    where
        P: std::hash::Hash + Eq + Clone,
    {
        if self.config.parallel_processing {
            self.parse_files_parallel(files).await
        } else {
            self.parse_files_sequential(files)
        }
    }

    async fn parse_files_parallel<P: AsRef<Path> + Send + 'static>(
        &self,
        files: Vec<(P, String)>,
    ) -> Result<HashMap<P, Vec<Symbol>>, Error>
    where
        P: std::hash::Hash + Eq + Clone,
    {
        let semaphore = Arc::new(Semaphore::new(self.config.max_parallel_tasks));
        let parser = Arc::new(self.clone());

        let mut results = HashMap::new();
        let handles: Vec<_> = stream::iter(files)
            .map(|(path, content)| {
                let parser = Arc::clone(&parser);
                let permit = Arc::clone(&semaphore).acquire_owned();
                let path = path.clone();
                
                async move {
                    let _permit = permit.await;
                    let symbols = parser.parse_file(path.as_ref(), &content)?;
                    Ok::<_, Error>((path, symbols))
                }
            })
            .buffered(self.config.max_parallel_tasks)
            .filter_map(|r| async move { r.ok() })
            .collect()
            .await;

        for (path, symbols) in handles {
            results.insert(path, symbols);
        }

        Ok(results)
    }

    fn parse_files_sequential<P: AsRef<Path>>(
        &self,
        files: Vec<(P, String)>,
    ) -> Result<HashMap<P, Vec<Symbol>>, Error>
    where
        P: std::hash::Hash + Eq,
    {
        let mut results = HashMap::new();
        for (path, content) in files {
            let symbols = self.parse_file(path.as_ref(), &content)?;
            results.insert(path, symbols);
        }
        Ok(results)
    }

    pub fn parse_file(&self, path: &Path, content: &str) -> Result<Vec<Symbol>, Error> {
        let language = path.extension()
            .and_then(|s| s.to_str())
            .ok_or_else(|| Error::UnsupportedLanguage("Missing file extension".to_string()))?;

        let lang = self.parsers.get(language)
            .ok_or_else(|| Error::UnsupportedLanguage(format!("Unsupported language: {}", language)))?;

        let tree = self.parse_content(content, lang)?;
        let mut symbols = self.extract_symbols(&tree, path, content)?;
        
        if self.config.scope_analysis {
            self.analyze_scopes(&mut symbols, &tree)?;
        }

        if self.config.track_references {
            self.process_references(&mut symbols, &tree, path, content)?;
        }

        Ok(symbols)
    }

    fn parse_content(&self, content: &str, lang: &Language) -> Result<tree_sitter::Tree, Error> {
        let mut parser = TsParser::new();
        parser
            .set_language(lang)
            .map_err(|e| Error::TreeSitter(e.to_string()))?;

        parser
            .parse(content, None)
            .ok_or_else(|| Error::Parse("Failed to parse file".to_string()))
    }

    fn analyze_scopes(
        &self,
        symbols: &mut [Symbol],
        tree: &tree_sitter::Tree,
    ) -> Result<(), Error> {
        // Create a scope walker and get all scopes from the tree
        let mut walker = ScopeWalker::new(tree.clone());
        let scopes = walker.analyze()
            .map_err(|e| Error::Parse(format!("Failed to analyze scopes: {}", e)))?;

        // Assign scopes to symbols based on their locations and build scope hierarchy
        for symbol in symbols {
            let mut matching_scopes: Vec<&Scope> = scopes.iter()
                .filter(|scope| scope.contains_line(symbol.location.start_line))
                .collect();

            // Sort scopes by size (smallest/most specific first)
            matching_scopes.sort_by_key(|scope| scope.end_line - scope.start_line);

            if let Some(most_specific_scope) = matching_scopes.first() {
                // Create a new scope with the complete hierarchy
                let mut current_scope = (*most_specific_scope).clone();
                
                // Build the scope hierarchy by finding parent scopes
                for potential_parent in matching_scopes.iter().skip(1) {
                    if potential_parent.contains_line(current_scope.start_line) 
                        && potential_parent.end_line >= current_scope.end_line {
                        current_scope = current_scope.with_parent((*potential_parent).clone());
                    }
                }
                
                symbol.scope = Some(current_scope);
            }
        }

        Ok(())
    }

    fn extract_signature(&self, node: Node, content: &str) -> Result<Option<String>, Error> {
        let signature = node
            .utf8_text(content.as_bytes())
            .map_err(|e| Error::Parse(e.to_string()))?
            .to_string();
        
        Ok(Some(signature))
    }

    fn extract_symbols(
        &self,
        tree: &tree_sitter::Tree,
        path: &Path,
        content: &str,
    ) -> Result<Vec<Symbol>, Error> {
        let mut symbols = Vec::new();
        let query = self.queries.get(path.extension()
            .and_then(|s| s.to_str())
            .ok_or_else(|| Error::UnsupportedLanguage("Unknown file extension".to_string()))?
        ).ok_or_else(|| Error::Parse("No query available for language".to_string()))?;

        let mut cursor = tree_sitter::QueryCursor::new();
        let mut matches = cursor.matches(query, tree.root_node(), content.as_bytes());

        while let Some(match_) = matches.next() {
            for capture in match_.captures {
                let capture_name = &query.capture_names()[capture.index as usize];
                if !capture_name.starts_with("name.definition.") {
                    continue;
                }

                let name = capture.node
                    .utf8_text(content.as_bytes())
                    .map_err(|e| Error::Parse(e.to_string()))?;

                let kind = match &capture_name["name.definition.".len()..] {
                    "function" => SymbolKind::Function,
                    "method" => SymbolKind::Method,
                    "class" => SymbolKind::Class,
                    "interface" => SymbolKind::Interface,
                    "struct" => SymbolKind::Struct,
                    "enum" => SymbolKind::Enum,
                    "constant" => SymbolKind::Constant,
                    "variable" => SymbolKind::Variable,
                    "module" => SymbolKind::Module,
                    "trait" => SymbolKind::Trait,
                    "type" => SymbolKind::TypeAlias,
                    "macro" => SymbolKind::Macro,
                    _ => continue,
                };

                let location = Location {
                    path: Rc::new(path.to_path_buf()),
                    start_line: capture.node.start_position().row + 1,
                    end_line: capture.node.end_position().row + 1,
                    start_col: capture.node.start_position().column,
                    end_col: capture.node.end_position().column,
                };

                let mut symbol = Symbol::new(name.to_string(), kind, location);
                if self.config.parse_signatures {
                    if let Ok(Some(signature)) = self.extract_signature(capture.node, content) {
                        symbol = symbol.with_signature(signature);
                    }
                }

                symbols.push(symbol);
            }
        }

        Ok(symbols)
    }

    fn process_references(
        &self,
        symbols: &mut [Symbol],
        tree: &tree_sitter::Tree,
        path: &Path,
        content: &str,
    ) -> Result<(), Error> {
        // Process references using node traversal
        let mut refs = Vec::new();
        self.extract_references_recursive(&tree.root_node(), content, path, &mut refs)?;

        // Add references to symbols with their types
        for (reference, ref_type) in refs {
            if let Some(symbol) = symbols.iter_mut().find(|s| s.name == reference.name) {
                // Only add non-definition references
                if ref_type != ReferenceType::Definition {
                    symbol.add_reference(reference);
                }
            }
        }

        Ok(())
    }

    fn extract_references_recursive(
        &self,
        node: &Node,
        content: &str,
        path: &Path,
        references: &mut Vec<(SymbolReference, ReferenceType)>,
    ) -> Result<(), Error> {
        // Process current node based on its kind
        match node.kind() {
            // Use declarations
            "use_declaration" => {
                if let Some(ref_) = self.process_reference(node, content, path, ReferenceType::Use)? {
                    references.push(ref_);
                }
            },
            
            // Function calls
            "call_expression" => {
                if let Some(function_name) = node.child_by_field_name("function") {
                    if let Some(ref_) = self.process_reference(&function_name, content, path, ReferenceType::Call)? {
                        references.push(ref_);
                    }
                }
            },
            
            // Type references
            "type_identifier" => {
                if let Some(ref_) = self.process_reference(node, content, path, ReferenceType::Type)? {
                    references.push(ref_);
                }
            },
            
            // Field access
            "field_expression" => {
                if let Some(field) = node.child_by_field_name("field") {
                    if let Some(ref_) = self.process_reference(&field, content, path, ReferenceType::Field)? {
                        references.push(ref_);
                    }
                }
            },
            
            // Module references
            "mod_item" => {
                if let Some(name) = node.child_by_field_name("name") {
                    if let Some(ref_) = self.process_reference(&name, content, path, ReferenceType::Module)? {
                        references.push(ref_);
                    }
                }
            },

            _ => {}
        }

        // Recursively process children
        let mut cursor = node.walk();
        if cursor.goto_first_child() {
            loop {
                let child = cursor.node();
                self.extract_references_recursive(&child, content, path, references)?;
                if !cursor.goto_next_sibling() {
                    break;
                }
            }
        }

        Ok(())
    }

    fn process_reference(
        &self,
        node: &Node,
        content: &str,
        path: &Path,
        ref_type: ReferenceType,
    ) -> Result<Option<(SymbolReference, ReferenceType)>, Error> {
        // Extract text and create reference
        let text = node.utf8_text(content.as_bytes())
            .map_err(|e| Error::Parse(e.to_string()))?;
        let name = text.to_string();

        let location = Location {
            path: Rc::new(path.to_path_buf()),
            start_line: node.start_position().row + 1,
            end_line: node.end_position().row + 1,
            start_col: node.start_position().column,
            end_col: node.end_position().column,
        };

        // Extract visibility and documentation
        let is_public = node.parent()
            .and_then(|n| n.child_by_field_name("pub"))
            .is_some();
        
        let has_docs = node.parent()
            .and_then(|n| n.prev_sibling())
            .map(|n| n.kind() == "line_comment" || n.kind() == "block_comment")
            .unwrap_or(false);

        // Determine kind based on ref_type and node context
        let kind = match ref_type {
            ReferenceType::Module => SymbolKind::Module,
            ReferenceType::Type => SymbolKind::TypeAlias,
            ReferenceType::Call => SymbolKind::Function,
            ReferenceType::Field => SymbolKind::Variable,
            ReferenceType::Use => {
                if node.kind() == "type_identifier" {
                    SymbolKind::TypeAlias
                } else {
                    SymbolKind::Variable
                }
            },
            ReferenceType::Definition => {
                match node.parent().map(|n| n.kind()) {
                    Some("function_item") => SymbolKind::Function,
                    Some("struct_item") => SymbolKind::Struct,
                    Some("impl_item") => SymbolKind::Class,
                    Some("trait_item") => SymbolKind::Trait,
                    Some("module") => SymbolKind::Module,
                    _ => SymbolKind::Variable,
                }
            },
        };

        Ok(Some((
            SymbolReference::new(name, location, kind)
                .with_visibility(is_public)
                .with_docs(has_docs),
            ref_type,
        )))
    }
}

impl Clone for Parser {
    fn clone(&self) -> Self {
        Self {
            parsers: self.parsers.clone(),
            queries: self.queries.clone(),
            config: self.config.clone(),
        }
    }
}

// Language functions for tree-sitter
fn language_rust() -> Language {
    tree_sitter_rust::LANGUAGE.into()
}

fn language_javascript() -> Language {
    tree_sitter_javascript::LANGUAGE.into()
}

fn language_python() -> Language {
    tree_sitter_python::LANGUAGE.into()
}

fn language_typescript() -> Language {
    tree_sitter_typescript::LANGUAGE_TYPESCRIPT.into()
}

fn language_c() -> Language {
    tree_sitter_c::LANGUAGE.into()
}

fn language_cpp() -> Language {
    tree_sitter_cpp::LANGUAGE.into()
}

fn language_csharp() -> Language {
    tree_sitter_c_sharp::LANGUAGE.into()
}

fn language_java() -> Language {
    tree_sitter_java::LANGUAGE.into()
}

fn language_go() -> Language {
    tree_sitter_go::LANGUAGE.into()
}

fn language_ruby() -> Language {
    tree_sitter_ruby::LANGUAGE.into()
}

fn language_php() -> Language {
    tree_sitter_php::LANGUAGE_PHP.into()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[tokio::test]
    async fn test_parallel_parsing() -> Result<(), Error> {
        let parser = Parser::new()?.with_config(
            ParseConfig::new()
                .with_parallel_processing(true)
                .with_max_parallel_tasks(2),
        );

        let files = vec![
            (
                PathBuf::from("test1.rs"),
                "pub fn test1() { test2(); }".to_string(),
            ),
            (
                PathBuf::from("test2.rs"),
                "pub fn test2() { }".to_string(),
            ),
        ];

        let results = parser.parse_files(files).await?;
        assert_eq!(results.len(), 2);
        
        Ok(())
    }

    #[test]
    fn test_scope_analysis() -> Result<(), Error> {
        let parser = Parser::new()?.with_config(
            ParseConfig::new()
                .with_scope_analysis(true)
        );

        let content = r#"
            mod test_mod {
                fn outer() {
                    fn inner() {
                        println!("test");
                    }
                }
            }
        "#;

        let symbols = parser.parse_file(&PathBuf::from("test.rs"), content)?;
        assert!(!symbols.is_empty());
        
        // Verify that scopes are assigned
        let module_symbol = symbols.iter().find(|s| s.kind == SymbolKind::Module);
        assert!(module_symbol.is_some());
        assert!(module_symbol.unwrap().scope.is_some());

        Ok(())
    }
}