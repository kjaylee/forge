use forge_language::{LanguageRegistry, RUST_CONFIG};

use crate::analyser::SymbolRanker;
use crate::error::RepoMapError;
use crate::symbol::{Symbol, SymbolIndex};
use crate::tree_context::TreeContext;
use std::cmp::min;
use std::collections::HashMap;

pub struct RepoMap {
    map_tokens: usize,
}

const REPOMAP_DEFAULT_TOKENS: usize = 1024;

impl RepoMap {
    pub fn new() -> Self {
        Self {
            map_tokens: REPOMAP_DEFAULT_TOKENS,
        }
    }

    pub fn with_map_tokens(mut self, map_tokens: usize) -> Self {
        self.map_tokens = map_tokens;
        self
    }

    pub async fn get_repo_map(&self, symbol_index: &SymbolIndex) -> Result<String, RepoMapError> {
        let repomap = self.get_ranked_symbols_map(self.map_tokens, symbol_index).await?;

        if repomap.is_empty() {
            println!("Warning: Empty repomap generated");
            // Return a minimal tree instead of error
            return Ok("No definitions found in repository\n".to_string());
        }

        println!("Repomap: {}k tokens", self.get_token_count(&repomap) / 1024);
        Ok(repomap)
    }

    fn get_token_count(&self, tree: &str) -> usize {
        let chars = tree.chars().count();
        let token_per_char_ratio = 0.25;
        let token_estimate = (chars as f64 * token_per_char_ratio) as usize;
        token_estimate
    }

    fn shread_tree(&self, ranked_symbols: Vec<Symbol>, max_map_tokens: usize) -> String {
        let num_symbols = ranked_symbols.len();

        let mut lower_bound = 0;
        let mut upper_bound = num_symbols;
        let mut best_tree = String::new();
        let mut best_tree_tokens = 0;
        let mut middle = min(max_map_tokens / 25, num_symbols);
        let mut iteration = 0;

        while lower_bound <= upper_bound {
            iteration += 1;

            let tree = RepoMap::to_tree(&ranked_symbols[..middle].to_vec());
            let num_tokens = self.get_token_count(&tree);


            if num_tokens < max_map_tokens && num_tokens > best_tree_tokens {
                best_tree.replace_range(.., &tree);
                best_tree_tokens = num_tokens;
            }

            if num_tokens < max_map_tokens {
                lower_bound = middle + 1;
            } else {
                upper_bound = middle - 1;
            }

            middle = (lower_bound + upper_bound) / 2;

        }
        best_tree
    }

    pub async fn get_ranked_symbols_map(
        &self,
        max_map_tokens: usize,
        symbol_index: &SymbolIndex,
    ) -> Result<String, RepoMapError> {
        let mut analyser = SymbolRanker::new(&symbol_index);       
        let ranked_symbols = analyser.get_ranked_symbols().clone(); 
        let tree = self.shread_tree(ranked_symbols, max_map_tokens);
        Ok(tree)
    }

    pub fn to_tree(symbols: &Vec<Symbol>) -> String {
        let mut symbols = symbols.clone();
        symbols.sort_by(|a, b| a.rel_fname.cmp(&b.rel_fname));
        symbols.push(Symbol::dummy());

        let mut output = String::new();

        let mut cur_fname = "";
        let mut cur_abs_fname = "";

        let mut lois: Option<Vec<usize>> = None;

        for symbol in &symbols {
            let this_rel_fname = symbol.rel_fname.to_str().expect("to_str to work for path");

            // check whether filename has changed, including first iteration
            if this_rel_fname != cur_fname {
                // take() resets the lois to None, inner_lois may be used as value for render_tree
                if let Some(inner_lois) = lois.take() {
                    output.push('\n');
                    output.push_str(&cur_abs_fname);
                    output.push_str(":\n");
                    let file_content = std::fs::read(&cur_abs_fname);
                    if let Err(_) = file_content {
                        continue;
                    }
                    let file_content = file_content.expect("file_content to be present");
                    // read the file content and keep track of it
                    output.push_str(&RepoMap::render_tree(
                        &cur_abs_fname,
                        &cur_fname,
                        &inner_lois,
                        &file_content,
                    ));
                } else if !cur_fname.is_empty() {
                    output.push('\n');
                    output.push_str(&cur_abs_fname);
                    output.push('\n');
                }

                lois = Some(Vec::new());
                cur_abs_fname = symbol.fname.to_str().unwrap();
                cur_fname = this_rel_fname;
            }

            // as_mut() is critical here as we want to mutate the original lois
            if let Some(lois) = lois.as_mut() {
                lois.push(symbol.line);
            }
        }

        output = output
            .lines()
            .map(|line| {
                if line.len() > 100 {
                    line[..100].to_string()
                } else {
                    line.to_string()
                }
            })
            .collect::<Vec<String>>()
            .join("\n");
        output.push('\n');

        output
    }

    pub fn render_tree(
        abs_fname: &str,
        _rel_fname: &str,
        lois: &Vec<usize>,
        file_content: &Vec<u8>,
    ) -> String {
        let mut code = String::from_utf8_lossy(file_content.as_slice()).to_string();
        if !code.ends_with('\n') {
            code.push('\n');
        }

        let registry = LanguageRegistry::global();

        let config = registry.for_file_path(abs_fname).unwrap().clone();
        let tree = config.get_tree_sitter_tree(code.as_bytes()).unwrap();
        let root_node = tree.root_node();
        let cursor = root_node.walk();

        // todo - consider using rel_fname
        let mut context = TreeContext::new(code, abs_fname.to_owned());

        context.init(cursor);

        context.add_lois(lois.clone());

        context.add_context();

        context.format()
    }
}