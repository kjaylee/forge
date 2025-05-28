use std::{fmt::Display, path::Path};

use super::models::{Block, Kind, Location, Offset, Span};
use tree_sitter::StreamingIterator;

const QUERIES: &'static str = include_str!("../queries/rust.scm");

/// Represents a query pattern with its associated metadata
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Pattern {
    Struct,
    Enum,
    Function,
}

impl Display for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str_repr = match self {
            Pattern::Struct => "struct.definition",
            Pattern::Enum => "enum.definition",
            Pattern::Function => "function.definition",
        };
        write!(f, "{}", str_repr)
    }
}

impl TryFrom<&str> for Pattern {
    type Error = anyhow::Error;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "struct.definition" => Ok(Pattern::Struct),
            "enum.definition" => Ok(Pattern::Enum),
            "function.definition" => Ok(Pattern::Function),
            _ => Err(anyhow::anyhow!("Unsupported pattern found '{}'", value)),
        }
    }
}

pub struct RustTreeSitter(tree_sitter::Parser);

impl Default for RustTreeSitter {
    fn default() -> Self {
        let mut parser = tree_sitter::Parser::new();
        parser
            .set_language(&tree_sitter_rust::LANGUAGE.into())
            .expect("shouldn't fail.");

        Self(parser)
    }
}

impl From<Pattern> for Kind {
    fn from(value: Pattern) -> Self {
        match value {
            Pattern::Struct => Kind::Struct,
            Pattern::Enum => Kind::Enum,
            Pattern::Function => Kind::Function,
        }
    }
}

impl RustTreeSitter {
    pub fn parse(&mut self, path: impl AsRef<Path>, source: &str) -> anyhow::Result<Vec<Block>> {
        let tree = self
            .0
            .parse(source, None)
            .ok_or(anyhow::anyhow!("Failed to parse code"))?;

        let query = tree_sitter::Query::new(&tree_sitter_rust::LANGUAGE.into(), QUERIES)?;

        // Execute query
        let mut cursor = tree_sitter::QueryCursor::new();
        let mut matches = cursor.matches(&query, tree.root_node(), source.as_bytes());

        let path_buf = path.as_ref().to_path_buf();
        let mut blocks = Vec::new();

        while let Some(match_) = matches.next() {
            // Get the matched node and its kind
            let capture = match_.captures[0];
            let node = capture.node;

            // Get the name of the capture from the query
            let capture_name = query.capture_names()[capture.index as usize];

            // Convert the capture name to a Pattern and then to a Kind
            let pattern = match Pattern::try_from(capture_name) {
                Ok(pattern) => pattern,
                Err(_) => continue, // Skip unknown patterns
            };

            // Extract the code snippet
            let start_byte = node.start_byte();
            let end_byte = node.end_byte();
            let snippet = source[start_byte..end_byte].to_string();

            // Create span for the block
            let span = Span {
                start: Location::from(node.start_position()),
                end: Location::from(node.end_position()),
            };

            blocks.push(Block::new(
                pattern.into(),
                path_buf.clone(),
                snippet,
                None,
                span,
                Offset { start: start_byte, end: end_byte },
            ));
        }

        Ok(blocks)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_rust_code() {
        // Sample Rust code to parse
        let sample_code = r#"
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

        let blocks = RustTreeSitter::default()
            .parse("./test.rs", sample_code)
            .unwrap();
        insta::assert_debug_snapshot!(blocks);
    }
}
