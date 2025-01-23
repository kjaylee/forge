use tree_sitter::Tree;

use crate::error::Result;
use crate::parser::Parser;
use crate::parser::ParsedSource;

#[derive(Debug, Clone)]
pub struct LanguageSyntaxConfig {
    /// A list of language names that can be processed by these scope queries
    /// e.g.: ["Typescript", "TSX"], ["Rust"]
    pub language_ids: &'static [&'static str],

    /// Extensions that can help classify the file: rs, js, tx, py, etc
    pub file_extensions: &'static [&'static str],

    /// tree-sitter grammar for this language
    pub grammar: tree_sitter::Language,

    /// Namespaces defined by this language,
    /// E.g.: type namespace, variable namespace, function namespace
    pub namespaces: Vec<Vec<String>>,

    /// The documentation query which will be used by this language
    pub documentation_query: Vec<String>,

    /// The queries to get the function body for the language
    pub function_query: Vec<String>,

    /// The different constructs for the language and their tree-sitter node types
    pub construct_types: Vec<String>,

    /// The different expression statements which are present in the language
    pub expression_statements: Vec<String>,

    /// The queries we use to get the class definitions
    pub class_query: Vec<String>,

    pub r#type_query: Vec<String>,

    /// The namespaces of the symbols which can be applied to a code symbols
    /// in case of typescript it can be `export` keyword
    pub namespace_types: Vec<String>,

    /// The comment prefix for the language, typescript is like // and rust
    /// is like //, python is like #
    pub comment_prefix: String,

    /// This is used to keep track of the end of line situations in many languages
    /// if they exist
    pub end_of_line: Option<String>,

    /// Tree sitter node types used to detect imports which are present in the file
    pub import_identifier_queries: String,

    /// Block start detection for the language
    pub block_start: Option<String>,

    /// Queries which help us figure out the variable identifiers so we can use go-to-definition
    /// on top of them
    pub variable_identifier_queries: Vec<String>,

    /// Generates the outline for the file which will be used to get the
    /// outline of the file
    pub outline_query: Option<String>,

    /// The file paths which need to be excluded when providing the
    /// type definitions
    pub excluded_file_paths: Vec<String>,

    /// The language string which can be used as an identifier for this language
    pub language_str: String,

    /// Used to specify which object a method or property belongs to.
    pub object_qualifier: String,

    /// Used to get the definitions for the file
    pub file_definitions_query: String,

    /// Required parameters of functions query
    pub required_parameter_types_for_functions: String,

    /// Grabs the span of a function call for example in rust: a.b.c.d(bllbbbbbb)
    /// this query can capture a.b.c.d
    pub function_call_path: Option<String>,
}

impl LanguageSyntaxConfig {
    /// Create a new parser instance for this language configuration
    pub fn parser(&self) -> Result<Parser> {
        Parser::new(self)
    }

    /// Check if this config supports a given file extension
    pub fn supports_extension(&self, extension: &str) -> bool {
        self.file_extensions.contains(&extension)
    }

    /// Check if this config supports a given language ID
    pub fn supports_language_id(&self, id: &str) -> bool {
        self.language_ids.contains(&id)
    }

    pub fn parse<'a>(&'a self, source: &'a [u8]) -> Result<ParsedSource<'a>> {
        let mut parser = self.parser()?;
        parser.parse(source)
    }
}

impl LanguageSyntaxConfig {
    pub fn get_tree_sitter_tree(&self, source_code: &[u8]) -> Option<Tree> {
        let grammar = &self.grammar;
        let mut parser = tree_sitter::Parser::new();
        parser.set_language(grammar).unwrap();
        parser.parse(source_code, None)
    }
    
}