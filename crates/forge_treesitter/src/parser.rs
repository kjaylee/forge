#![allow(dead_code)]
use std::{fmt::Display, path::Path};

use tree_sitter::{Parser as TreeSitterParser, StreamingIterator};

use crate::{Block, Kind, Offset, SiblingKind};

pub struct Parser {
    parser: TreeSitterParser,
    language: SupportedLanguage,
}

impl TryFrom<&str> for Parser {
    type Error = anyhow::Error;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let language = match value.to_lowercase().as_str() {
            "rs" => SupportedLanguage::Rust,
            _ => {
                return Err(anyhow::anyhow!(format!(
                    "Unsupported '{}' language extension",
                    value
                )));
            }
        };
        Ok(Parser::from(language))
    }
}

#[derive(Clone)]
pub enum SupportedLanguage {
    Rust,
}

impl Display for SupportedLanguage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SupportedLanguage::Rust => write!(f, "rust"),
        }
    }
}

impl TryFrom<SupportedLanguage> for tree_sitter::Query {
    type Error = anyhow::Error;
    fn try_from(value: SupportedLanguage) -> Result<Self, Self::Error> {
        let queries = value.queries();
        let language = tree_sitter::Language::from(&value);
        let query = tree_sitter::Query::new(&language, queries)?;
        Ok(query)
    }
}

impl SupportedLanguage {
    pub fn queries(&self) -> &'static str {
        match self {
            SupportedLanguage::Rust => include_str!("queries/rust.scm"),
        }
    }
}

impl From<&SupportedLanguage> for tree_sitter::Language {
    fn from(value: &SupportedLanguage) -> Self {
        match value {
            SupportedLanguage::Rust => tree_sitter_rust::LANGUAGE.into(),
        }
    }
}

impl From<SupportedLanguage> for Parser {
    fn from(value: SupportedLanguage) -> Self {
        let mut parser = tree_sitter::Parser::new();
        parser
            .set_language(&tree_sitter::Language::from(&value))
            .expect(format!("Failed to set '{}' language for tree-sitter parser", value).as_str());
        Self { parser, language: value }
    }
}

impl Parser {
    pub fn parse(&mut self, path: &Path, code: &str) -> anyhow::Result<Vec<Block>> {
        let tree = self
            .parser
            .parse(code, None)
            .ok_or(anyhow::anyhow!("Failed to parse code"))?;
        let root_node = tree.root_node();
        let query = tree_sitter::Query::try_from(self.language.clone())?;

        // Execute query
        let mut cursor = tree_sitter::QueryCursor::new();
        let mut matches = cursor.matches(&query, root_node, code.as_bytes());

        let path_buf = path.to_path_buf();
        let mut blocks = Vec::new();

        while let Some(match_) = matches.next() {
            for capture in match_.captures {
                let node = capture.node;
                let capture_name = query.capture_names()[capture.index as usize];

                // Convert the capture name to a Pattern and then to a Kind
                let pattern = match Kind::try_from(capture_name) {
                    Ok(pattern) => pattern,
                    Err(_) => continue, // Skip unknown patterns
                };

                // Look for the start of preceding line comments/attribute_item for supported kinds
                let mut base_start_byte = None;
                if let Some(prev_sibling) = node.prev_sibling() {
                    let mut current = Some(prev_sibling);
                    while let Some(node) = current {
                        if let Ok(_) = SiblingKind::try_from(node.kind()) {
                            base_start_byte = Some(node.start_byte());
                            current = node.prev_sibling();
                        } else {
                            break;
                        }
                    }
                }

                // Extract the code snippet safely handling UTF-8
                let start_byte = node.start_byte();
                let end_byte = node.end_byte();

                // Calculate character offsets
                let start_char = base_start_byte
                    .map_or(code[..start_byte].chars().count(), |base_byte| {
                        code[..base_byte].chars().count()
                    });
                let end_char = code[..end_byte].chars().count();

                // Extract snippet using character offsets
                let snippet: String = code
                    .chars()
                    .skip(start_char)
                    .take(end_char - start_char)
                    .collect();

                if snippet.is_empty() {
                    continue;
                }

                // Store character offsets
                let offset = Offset { start: start_char, end: end_char };

                blocks.push(Block::new(pattern, path_buf.clone(), snippet, offset));
            }
        }

        Ok(blocks)
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::*;

    #[test]
    fn test_parse_rust_code() {
        // Sample Rust code to parse
        let sample_code = r#"
            /// wrapper type with error of string type.
            type Result<I> = std::result::Result<I, String>;

            const DATA: &'static str = "test";
            /// Represents user information
            /// in the system
            struct User {
                name: String,
                age: u32,
            }
            
            /// type of status supported by system
            enum Status {
                Active,
                Inactive,
                Pending,
            }
            
            impl Status {
                /// returns the status reference
                pub fn status(&self) -> &Status {
                    self
                }
            }

            #[test]
            /// process user in test env.
            fn process_user(user: &User) -> Status {
                if user.age > 18 {
                    Status::Active
                } else {
                    Status::Pending
                }
            }
        "#;

        let blocks = Parser::from(SupportedLanguage::Rust)
            .parse(&PathBuf::from("./test.rs"), sample_code)
            .unwrap();
        insta::assert_debug_snapshot!(blocks);
    }
}
