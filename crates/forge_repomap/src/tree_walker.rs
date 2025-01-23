use forge_language::LanguageSyntaxConfig;
use std::collections::HashSet;
use std::mem::MaybeUninit;
use std::path::Path;
use tree_sitter::TreeCursor;
use crate::tree_context::TreeContext;
use crate::error::RepoMapError;

#[derive(Debug, Clone)]
pub struct NodeInfo {
    kind: String,
    text: String,
    start_line: usize,
    end_line: usize,
}

pub struct TreeWalker {
    config: LanguageSyntaxConfig,
    code: String,
    lines_of_interest: HashSet<usize>,
    nodes: Vec<Vec<NodeInfo>>,
    scopes: Vec<HashSet<usize>>,
    header: Vec<Vec<(usize, usize, usize)>>,
}

impl TreeWalker {
    pub fn new(config: LanguageSyntaxConfig, code: String) -> Self {
        let num_lines = code.lines().count() + 1;
        Self {
            config,
            code,
            lines_of_interest: HashSet::new(),
            nodes: (0..num_lines).map(|_| Vec::new()).collect(),
            scopes: vec![HashSet::new(); num_lines],
            header: vec![Vec::new(); num_lines],
        }
    }

    pub fn add_line_of_interest(&mut self, line: usize) {
        self.lines_of_interest.insert(line);
    }

    pub fn add_lines_of_interest(&mut self, lines: &[usize]) {
        self.lines_of_interest.extend(lines.iter());
    }

    pub fn get_nodes(&self) -> &Vec<Vec<NodeInfo>> {
        &self.nodes
    }

    pub fn get_nodes_for_line(&self, line: usize) -> &Vec<NodeInfo> {
        &self.nodes[line]
    }

    pub fn get_scopes(&self) -> &Vec<HashSet<usize>> {
        &self.scopes
    }

    pub fn get_headers(&self) -> &Vec<Vec<(usize, usize, usize)>> {
        &self.header
    }

    fn process_node(&mut self, node: tree_sitter::Node, code: &[u8]) {
        let start_line = node.start_position().row;
        let end_line = node.end_position().row;
        let size = end_line - start_line;

        // Store node information
        let node_info = NodeInfo {
            kind: node.kind().to_string(),
            text: node.utf8_text(code).unwrap_or("").to_string(),
            start_line,
            end_line,
        };

        self.nodes[start_line].push(node_info);

        if size > 0 {
            self.header[start_line].push((size, start_line, end_line));
        }

        for i in start_line..=end_line {
            self.scopes[i].insert(start_line);
        }
    }

    fn walk_with_cursor<'a>(&mut self, mut cursor: TreeCursor<'a>, code: &[u8]) {
        loop {
            self.process_node(cursor.node(), code);

            // Try to move to the first child
            if cursor.goto_first_child() {
                continue;
            }

            // If no children, try to move to the next sibling
            if cursor.goto_next_sibling() {
                continue;
            }

            // If no next sibling, go up the tree
            loop {
                if !cursor.goto_parent() {
                    // We've reached the root again, we're done
                    return;
                }

                // go to next sibling, break to continue outer loop
                if cursor.goto_next_sibling() {
                    break;
                }
            }
        }
    }

    pub fn walk_ast(&mut self) -> Result<(), RepoMapError> {
        // Take ownership of config temporarily using MaybeUninit
        let mut uninit = MaybeUninit::uninit();
        let config = std::mem::replace(&mut self.config, unsafe { uninit.assume_init() });
        let code = self.code.as_bytes().to_vec();
        
        let result = {
            let mut parser = config.parser()
                .map_err(|e| RepoMapError::ParseError(e.to_string()))?;
                
            let tree = parser.parse(&code)
                .map_err(|e| RepoMapError::ParseError(e.to_string()))?;

            let cursor = tree.root_node().walk();
            self.walk_with_cursor(cursor, &code);
            Ok(())
        };

        // Restore config
        self.config = config;
        result
    }

    pub fn walk(&self, file_path: &Path) -> Result<String, RepoMapError> {
        let mut parser = self.config.parser()
            .map_err(|e| RepoMapError::ParseError(e.to_string()))?;
            
        let parsed = parser.parse(self.code.as_bytes())
            .map_err(|e| RepoMapError::ParseError(e.to_string()))?;

        let cursor = parsed.tree().root_node().walk();
        let mut context = TreeContext::new(
            self.code.clone(),
            file_path.to_string_lossy().to_string(),
        );

        context.init(cursor);
        context.add_lois(self.lines_of_interest.iter().cloned().collect());
        context.add_context();

        Ok(context.format())
    }

    pub fn get_lines_of_interest(&self) -> &HashSet<usize> {
        &self.lines_of_interest
    }

    pub fn get_code(&self) -> &str {
        &self.code
    }
}