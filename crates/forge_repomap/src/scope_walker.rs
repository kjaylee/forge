use tree_sitter::{Node, Tree};
use crate::symbol::{Scope, ScopeType};

pub struct ScopeWalker {
    tree: Tree,
}

impl ScopeWalker {
    pub fn new(tree: Tree) -> Self {
        Self { tree }
    }

    pub fn analyze(&mut self) -> Result<Vec<Scope>, String> {
        let mut scopes = Vec::new();
        self.analyze_node(&self.tree.root_node(), &mut scopes)?;
        Ok(scopes)
    }

    fn analyze_node(&self, node: &Node, scopes: &mut Vec<Scope>) -> Result<(), String> {
        let mut cursor = node.walk();

        // First check if current node is a scope
        if let Some(scope_type) = self.get_scope_type(node) {
            let scope = self.create_scope(node, scope_type);
            scopes.push(scope);
        }

        // Recursively process children
        if cursor.goto_first_child() {
            loop {
                let child = cursor.node();
                self.analyze_node(&child, scopes)?;
                if !cursor.goto_next_sibling() {
                    break;
                }
            }
        }

        Ok(())
    }

    fn create_scope(&self, node: &Node, scope_type: ScopeType) -> Scope {
        let mut scope = Scope::new(
            scope_type,
            node.start_position().row + 1,
            node.end_position().row + 1,
        );

        // Find parent scope if any using cursor
        let mut cursor = node.walk();
        if cursor.goto_parent() {
            while let Some(parent_type) = self.get_scope_type(&cursor.node()) {
                let parent_node = cursor.node();
                scope = scope.with_parent(Scope::new(
                    parent_type,
                    parent_node.start_position().row + 1,
                    parent_node.end_position().row + 1,
                ));
                if !cursor.goto_parent() {
                    break;
                }
            }
        }

        scope
    }

    fn get_scope_type(&self, node: &Node) -> Option<ScopeType> {
        match node.kind() {
            "source_file" => Some(ScopeType::Module),
            "function_item" | "function_definition" => Some(ScopeType::Function),
            "block" => Some(ScopeType::Block),
            "struct_item" | "class_definition" => Some(ScopeType::Class),
            "trait_item" | "interface_declaration" => Some(ScopeType::Interface),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tree_sitter::Parser;

    fn setup_tree(source: &str) -> Tree {
        let mut parser = Parser::new();
        let language: tree_sitter::Language = tree_sitter_rust::LANGUAGE.into();
        parser.set_language(&language).unwrap();
        parser.parse(source, None).unwrap()
    }

    #[test]
    fn test_scope_walker_basic() {
        let source = r#"
            pub fn test_function() {
                let x = 1;
            }
        "#;

        let tree = setup_tree(source);
        let mut walker = ScopeWalker::new(tree);
        let scopes = walker.analyze().unwrap();

        let function_scope = scopes.iter()
            .find(|s| s.scope_type == ScopeType::Function)
            .expect("Should find function scope");

        assert_eq!(function_scope.scope_type, ScopeType::Function);
        assert_eq!(function_scope.start_line, 2);
        assert!(function_scope.parent_scope.is_none());
    }

    #[test]
    fn test_scope_nesting() {
        let source = r#"
            fn outer() {
                fn inner() {
                    let x = 1;
                }
            }
        "#;

        let tree = setup_tree(source);
        let mut walker = ScopeWalker::new(tree);
        let scopes = walker.analyze().unwrap();

        // Get function scopes only
        let function_scopes: Vec<_> = scopes.iter()
            .filter(|s| s.scope_type == ScopeType::Function)
            .collect();

        // Separate nested and top-level functions
        let nested_functions: Vec<_> = function_scopes.iter()
            .filter(|s| s.parent_scope.is_some())
            .collect();
        let top_level_functions: Vec<_> = function_scopes.iter()
            .filter(|s| s.parent_scope.is_none())
            .collect();

        assert_eq!(nested_functions.len(), 1, "Should have one nested function");
        assert_eq!(top_level_functions.len(), 1, "Should have one top-level function");

        // Get all function scopes
        let function_scopes: Vec<_> = scopes.iter()
            .filter(|s| s.scope_type == ScopeType::Function)
            .collect();

        // Find nested and outer functions
        let inner_fn = function_scopes.iter()
            .find(|s| s.start_line == 3)
            .expect("Should find inner function at line 3");
        
        let outer_fn = function_scopes.iter()
            .find(|s| s.start_line == 2)
            .expect("Should find outer function at line 2");

        // Verify proper nesting
        assert!(inner_fn.parent_scope.is_some(), "Inner function should have a parent");
        assert!(outer_fn.parent_scope.is_none(), "Outer function should not have a parent");
        assert_eq!(inner_fn.parent_scope.as_ref().unwrap().start_line, 2,
            "Inner function's parent should be the outer function");
    }
}