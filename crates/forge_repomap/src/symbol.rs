use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use forge_language::{
    LanguageRegistry, LanguageSyntaxConfig, QueryEngine, 
};

use super::error::RepoMapError;

#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct Symbol {
    pub rel_fname: PathBuf,
    pub fname: PathBuf,
    pub line: usize,
    pub name: String,
    pub kind: SymbolKind,
}

impl Symbol {
    pub fn new(
        rel_fname: PathBuf,
        fname: PathBuf,
        line: usize,
        name: String,
        kind: SymbolKind,
    ) -> Self {
        Self {
            rel_fname,
            fname,
            line,
            name,
            kind,
        }
    }

    pub fn dummy() -> Self {
        Self {
            rel_fname: PathBuf::new(),
            fname: PathBuf::new(),
            line: 0,
            name: "".to_owned(),
            kind: SymbolKind::Definition,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum SymbolKind {
    Definition,
    Reference,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct SymbolIndex {
    pub defines: HashMap<String, HashSet<PathBuf>>,
    pub references: HashMap<String, Vec<PathBuf>>, // Using Vec to maintain order of references
    pub definitions: HashMap<(PathBuf, String), HashSet<Symbol>>,
    pub common_symbols: HashSet<String>,
    pub file_to_symbols: HashMap<PathBuf, HashSet<(PathBuf, String)>>,
    pub path: PathBuf,
}

impl SymbolIndex {
    pub fn new(path: &Path) -> Self {
        Self {
            defines: HashMap::new(),
            references: HashMap::new(),
            definitions: HashMap::new(),
            common_symbols: HashSet::new(),
            file_to_symbols: HashMap::new(),
            path: path.to_path_buf(),
        }
    }

    pub async fn generate_from_files(&mut self, files: HashMap<String, Vec<u8>>) {
        
        // Get language registry
        let registry = LanguageRegistry::global();
        

        for (file_str, content) in files {
            let file = file_str.clone();
            // Get file extension
            let config = registry.for_file_path(&file);
            if let Some(config) = config {
                match self.process_file(&file, &content, config) {
                    Ok(symbols) => {
                        for symbol in symbols {
                            self.add_symbol(symbol, &PathBuf::from(&file));
                        } 
                    },
                    Err(e) =>  {eprintln!("Error processing file {}: {}", file, e);}
                    
                }
                
        }
    }
        self.post_process_symbols();
    }

    fn process_file(&self, fname: &str, content: &[u8], config: &'static LanguageSyntaxConfig) -> Result<Vec<Symbol>, RepoMapError> {
            
        let rel_path = self.get_rel_fname(&PathBuf::from(fname));
        let mut symbols = Vec::new();
        
        // Create QueryEngine for handling both definition and reference queries
        let mut query_engine = QueryEngine::from_config(config)
            .map_err(|e| RepoMapError::ParseError(e.to_string()))?;


        // Process definitions using file_definitions_query
        self.process_definitions(
            &mut query_engine,
            &config.file_definitions_query,
            fname,
            &rel_path,
            content,
            &mut symbols,
            &config
        )?;
        
        Ok(symbols)
    }

    fn process_definitions(
        &self,
        query_engine: &mut QueryEngine,
        query_str: &str,
        fname: &str,
        rel_path: &Path,
        source: &[u8],
        symbols: &mut Vec<Symbol>,
        config: &'static LanguageSyntaxConfig
    ) -> Result<(), RepoMapError> {
        let tree = config.get_tree_sitter_tree(source).ok_or(RepoMapError::ParseError("temp todo".to_string()))?;
        let root_node = tree.root_node();
        
        let matches = query_engine.execute(query_str, root_node,source)
            .map_err(|e| RepoMapError::ParseError(e.to_string()))?;


        for query_match in matches {
            let captures = &query_match.captures;

            // Find definition captures
            for capture in captures { 

                // Process only definition nodes
                if capture.name.contains(".definition.") {
                    // Look for a corresponding name node
                    if let Some(name_capture) = captures.iter().find(|c| 
                        c.name.starts_with("name.definition.")) {
                            
                        let start = name_capture.node.start_position();
                        let node_text = name_capture.node.utf8_text(source)
                            .map_err(|e| RepoMapError::ParseError(e.to_string()))?;
                        
                        
                        symbols.push(Symbol::new(
                            rel_path.to_path_buf(),
                            PathBuf::from(fname),
                            start.row + 1,
                            node_text.to_string(),
                            SymbolKind::Definition,
                        ));
                    }
                } else if capture.name.starts_with("name.reference.") {
                    if let Ok(node_text) = capture.node.utf8_text(source) {
                        let start = capture.node.start_position();
                        
                        symbols.push(Symbol::new(
                            rel_path.to_path_buf(),
                            PathBuf::from(fname),
                            start.row + 1,
                            node_text.to_string(),
                            SymbolKind::Reference,
                        ));
                    } else {
                        println!("  Failed to get text for reference with name: {}", capture.name);
                    }
                }
            }
        }
        Ok(())
    }

    pub fn add_symbol(&mut self, symbol: Symbol, rel_path: &PathBuf) {
        match symbol.kind {
            SymbolKind::Definition => {
                self.defines
                    .entry(symbol.name.clone())
                    .or_default()
                    .insert(rel_path.clone());
                self.definitions
                    .entry((rel_path.clone(), symbol.name.clone()))
                    .or_default()
                    .insert(symbol.clone());
                self.file_to_symbols
                    .entry(rel_path.clone())
                    .or_default()
                    .insert((rel_path.clone(), symbol.name.clone()));
            }
            SymbolKind::Reference => {
                // Keep references in a Vec to maintain insertion order
                self.references
                    .entry(symbol.name.clone())
                    .or_default()
                    .push(rel_path.clone());

                self.file_to_symbols
                    .entry(rel_path.clone())
                    .or_default()
                    .insert((rel_path.clone(), symbol.name.clone()));
            }
        }
    }

    pub fn post_process_symbols(&mut self) {
        self.process_empty_references();
        self.process_common_symbols();
    }

    pub fn process_empty_references(&mut self) {
        if self.references.is_empty() {
            self.references = self
                .defines
                .iter()
                .map(|(k, v)| (k.clone(), v.iter().cloned().collect::<Vec<PathBuf>>()))
                .collect();
        }
    }

    pub fn process_common_symbols(&mut self) {
        self.common_symbols = self
            .defines
            .keys()
            .filter_map(|key| {
                if self.references.contains_key(key) {
                    Some(key.clone())
                } else {
                    None
                }
            })
            .collect();
    }

    pub fn get_rel_fname(&self, fname: &PathBuf) -> PathBuf {
        fname
            .strip_prefix(&self.path)
            .unwrap_or(fname)
            .to_path_buf()
    }

    pub fn definitions(&self) -> &HashMap<(PathBuf, String), HashSet<Symbol>> {
        &self.definitions
    }
}
