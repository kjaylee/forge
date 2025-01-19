use std::collections::HashMap;
use std::path::Path;
use tree_sitter::{Language, Parser as TsParser, Query};
use streaming_iterator::StreamingIterator;

use crate::error::Error;
use crate::symbol::{Symbol, SymbolKind, Location};

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
    // Use JavaScript for TypeScript as they share similar syntax
    tree_sitter_javascript::LANGUAGE.into()
}

pub struct Parser {
    parsers: HashMap<String, Language>,
    queries: HashMap<String, Query>,
}

impl Parser {
    pub fn new() -> Result<Self, Error> {
        let mut parsers = HashMap::new();
        let mut queries = HashMap::new();

        // Initialize parsers
        parsers.insert("rust".to_string(), language_rust());
        parsers.insert("javascript".to_string(), language_javascript());
        parsers.insert("python".to_string(), language_python());
        parsers.insert("typescript".to_string(), language_typescript());

        // Load queries from embedded files in the lang directory
        Self::load_query(&mut queries, "rust", include_str!("lang/rust.scm"))?;
        Self::load_query(&mut queries, "javascript", include_str!("lang/javascript.scm"))?;
        Self::load_query(&mut queries, "python", include_str!("lang/python.scm"))?;
        Self::load_query(&mut queries, "typescript", include_str!("lang/typescript.scm"))?;

        Ok(Self {
            parsers,
            queries,
        })
    }

    fn load_query(queries: &mut HashMap<String, Query>, language: &str, query_source: &str) -> Result<(), Error> {
        if let Some(lang) = get_language(language) {
            let query = Query::new(&lang, query_source)
                .map_err(|e| Error::Parse(format!("Failed to parse {} query: {}", language, e)))?;
            queries.insert(language.to_string(), query);
            Ok(())
        } else {
            Err(Error::UnsupportedLanguage(language.to_string()))
        }
    }

    pub fn parse_file(&self, path: &Path, content: &str) -> Result<Vec<Symbol>, Error> {
        let language = self.detect_language(path)?;
        let lang = self.parsers.get(language)
            .ok_or_else(|| Error::UnsupportedLanguage(language.to_string()))?;

        let mut parser = TsParser::new();
        parser.set_language(lang)
            .map_err(|e| Error::TreeSitter(e.to_string()))?;

        let tree = parser.parse(content, None)
            .ok_or_else(|| Error::Parse("Failed to parse file".to_string()))?;

        let query = self.queries.get(language)
            .ok_or_else(|| Error::Parse(format!("No query available for language: {}", language)))?;

        let mut symbols = Vec::new();

        // Extract symbols using the appropriate query
        let mut query_cursor = tree_sitter::QueryCursor::new();
        let mut cursor = query_cursor.matches(query, tree.root_node(), content.as_bytes());
        while let Some(match_) = cursor.next() {
            for capture in match_.captures {
                let capture_name = &query.capture_names()[capture.index as usize].to_string();
                let node = capture.node;

                if let Some(symbol) = self.create_symbol(capture_name, node, path, content)? {
                    symbols.push(symbol);
                }
            }
        }

        Ok(symbols)
    }

    fn detect_language(&self, path: &Path) -> Result<&str, Error> {
        match path.extension().and_then(|s| s.to_str()) {
            Some("rs") => Ok("rust"),
            Some("js") => Ok("javascript"),
            Some("py") => Ok("python"),
            Some("ts") | Some("tsx") => Ok("typescript"),
            _ => Err(Error::UnsupportedLanguage(format!("Unsupported file extension: {:?}", path.extension()))),
        }
    }

    fn create_symbol(
        &self,
        capture_name: &str,
        node: tree_sitter::Node,
        file_path: &Path,
        source: &str,
    ) -> Result<Option<Symbol>, Error> {
        let name = node.utf8_text(source.as_bytes())
            .map_err(|e| Error::Parse(e.to_string()))?
            .to_string();

        let kind = match capture_name {
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
            "implementation" => SymbolKind::Implementation,
            _ => return Ok(None),
        };

        let location = Location {
            path: file_path.to_path_buf(),
            start_line: node.start_position().row + 1,
            end_line: node.end_position().row + 1,
            start_col: node.start_position().column,
            end_col: node.end_position().column,
        };

        Ok(Some(Symbol::new(name, kind, location)))
    }
}

fn get_language(language: &str) -> Option<Language> {
    match language {
        "rust" => Some(language_rust()),
        "javascript" => Some(language_javascript()),
        "python" => Some(language_python()),
        "typescript" => Some(language_typescript()),
        _ => None,
    }
}