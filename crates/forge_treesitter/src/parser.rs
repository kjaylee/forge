#![allow(dead_code)]
use std::path::Path;

use tree_sitter::{Parser as TreeSitterParser, StreamingIterator};

use crate::{Block, Kind, Offset};

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

impl TryFrom<SupportedLanguage> for tree_sitter::Query {
    type Error = anyhow::Error;
    fn try_from(value: SupportedLanguage) -> Result<Self, Self::Error> {
        let queries = value.queries();
        let language: tree_sitter::Language = value.into();
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

impl From<SupportedLanguage> for tree_sitter::Language {
    fn from(value: SupportedLanguage) -> Self {
        match value {
            SupportedLanguage::Rust => tree_sitter_rust::LANGUAGE.into(),
        }
    }
}

impl From<SupportedLanguage> for Parser {
    fn from(value: SupportedLanguage) -> Self {
        let mut parser = tree_sitter::Parser::new();
        parser
            .set_language(&value.clone().into())
            .expect("Failed to set Rust language for tree-sitter parser");
        Self { parser, language: value }
    }
}

impl Parser {
    pub fn parse(&mut self, path: &Path, code: &str) -> anyhow::Result<Vec<Block>> {
        let tree = self
            .parser
            .parse(code, None)
            .ok_or(anyhow::anyhow!("Failed to parse code"))?;
        let query = tree_sitter::Query::try_from(self.language.clone())?;

        // Execute query
        let mut cursor = tree_sitter::QueryCursor::new();
        let mut matches = cursor.matches(&query, tree.root_node(), code.as_bytes());

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

                // Extract the code snippet
                let start_byte = node.start_byte();
                let end_byte = node.end_byte();
                let snippet = code[start_byte..end_byte].to_string();

                let offset = Offset { start: start_byte, end: end_byte };

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
            const DATA: &'static str = "test";
            struct User {
                name: String,
                age: u32,
            }
            
            enum Status {
                Active,
                Inactive,
                Pending,
            }
            
            impl Status {
                pub fn status(&self) -> &Status {
                    self
                }
            }

            #[test]
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
