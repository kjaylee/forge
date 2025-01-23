use tree_sitter::{Parser as TreeSitterParser, Tree};
use crate::error::{LanguageError, Result};
use crate::language::LanguageSyntaxConfig;
use std::marker::PhantomData;

pub struct Parser<'a> {
    inner: TreeSitterParser,
    config: &'a LanguageSyntaxConfig,
}

pub struct ParsedSource<'a> {
    pub(crate) tree: Tree,
    pub(crate) source: &'a [u8],
    _marker: PhantomData<&'a ()>,
}

impl<'a> Parser<'a> {
    pub fn new(config: &'a LanguageSyntaxConfig) -> Result<Self> {
        let mut parser = TreeSitterParser::new();
        let language = &config.grammar;
        
        parser.set_language(&language)
            .map_err(|e| LanguageError::ParserInitError(e.to_string()))?;
            
        Ok(Self {
            inner: parser,
            config,
        })
    }

    pub fn parse(&mut self, source: &'a [u8]) -> Result<ParsedSource<'a>> {
        let tree = self.inner
            .parse(source, None)
            .ok_or_else(|| LanguageError::ParseError("Failed to parse source".into()))?;
        Ok(ParsedSource { 
            tree, 
            source,
            _marker: PhantomData,
        })
    }
    
    pub fn config(&self) -> &'a LanguageSyntaxConfig {
        self.config
    }
}

impl<'a> ParsedSource<'a> {
    pub fn tree(&self) -> &Tree {
        &self.tree
    }
    
    pub fn source(&self) -> &'a [u8] {
        self.source
    }
    
    pub fn root_node(&self) -> tree_sitter::Node {
        self.tree.root_node()
    }
}