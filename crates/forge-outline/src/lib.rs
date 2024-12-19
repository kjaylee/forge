use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use tree_sitter::{Language, Parser, Query, QueryCursor};

mod error;
use error::{Error, Result};

fn load_language_parser(language_name: &str) -> Result<Language> {
    match language_name {
        "rust" => Ok(tree_sitter_rust::language()),
        "javascript" => Ok(tree_sitter_javascript::language()),
        "python" => Ok(tree_sitter_python::language()),
        x => Err(Error::LanguageError(format!("Unsupported language: {}", x))),
    }
}

fn load_queries() -> HashMap<&'static str, &'static str> {
    let mut queries = HashMap::new();
    queries.insert(
        "rust",
        r#"
            (struct_item
                name: (type_identifier) @name.definition.class) @definition.class

            (declaration_list
                (function_item
                    name: (identifier) @name.definition.method)) @definition.method

            (function_item
                name: (identifier) @name.definition.function) @definition.function
        "#,
    );
    queries.insert(
        "javascript",
        r#"
            (
                (comment)* @doc
                .
                (method_definition
                    name: (property_identifier) @name) @definition.method
                (#not-eq? @name "constructor")
                (#strip! @doc "^[\\s\\*/]+|^[\\s\\*/]$")
                (#select-adjacent! @doc @definition.method)
            )

            (
                (comment)* @doc
                .
                [
                    (class
                        name: (_) @name)
                    (class_declaration
                        name: (_) @name)
                ] @definition.class
                (#strip! @doc "^[\\s\\*/]+|^[\\s\\*/]$")
                (#select-adjacent! @doc @definition.class)
            )

            (
                (comment)* @doc
                .
                [
                    (function_declaration
                        name: (identifier) @name)
                    (generator_function_declaration
                        name: (identifier) @name)
                ] @definition.function
                (#strip! @doc "^[\\s\\*/]+|^[\\s\\*/]$")
                (#select-adjacent! @doc @definition.function)
            )

            (
                (comment)* @doc
                .
                (lexical_declaration
                    (variable_declarator
                        name: (identifier) @name
                        value: [(arrow_function) (function_expression)]) @definition.function)
                (#strip! @doc "^[\\s\\*/]+|^[\\s\\*/]$")
                (#select-adjacent! @doc @definition.function)
            )

            (
                (comment)* @doc
                .
                (variable_declaration
                    (variable_declarator
                        name: (identifier) @name
                        value: [(arrow_function) (function_expression)]) @definition.function)
                (#strip! @doc "^[\\s\\*/]+|^[\\s\\*/]$")
                (#select-adjacent! @doc @definition.function)
            )
        "#,
    );
    queries.insert(
        "python",
        r#"
            (class_definition
                name: (identifier) @name.definition.class) @definition.class

            (function_definition
                name: (identifier) @name.definition.function) @definition.function
        "#,
    );
    // Add more queries for other languages
    queries
}

fn parse_file(file: &Path, parser: &mut Parser, query: &Query) -> Option<String> {
    let content = fs::read_to_string(file).ok()?;
    let tree = parser.parse(&content, None)?;

    let mut cursor = QueryCursor::new();
    let mut captures: Vec<_> = cursor
        .matches(query, tree.root_node(), content.as_bytes())
        .flat_map(|m| m.captures)
        .filter_map(|capture| {
            let capture_name = &query.capture_names()[capture.index as usize];
            if !capture_name.contains("name") {
                return None;
            }
            let node = capture.node;
            let parent = node.parent()?;
            // Skip impl blocks and other non-definition nodes
            if parent.kind() == "impl_item" {
                return None;
            }
            Some((node.start_position().row, parent))
        })
        .collect();

    // Sort captures by their start position
    captures.sort_by_key(|&(row, _)| row);

    let lines: Vec<&str> = content.lines().collect();
    let mut formatted_output = String::new();
    let mut last_line = -1;
    let mut seen_lines = HashSet::new();

    for (start_line, _) in captures {
        // Skip if we've already processed this line
        if !seen_lines.insert(start_line) {
            continue;
        }

        // Add separator if there's a gap between captures
        if last_line != -1 && start_line as i32 > last_line + 1 {
            formatted_output.push_str("|----\n");
        }

        // Only add the first line of the definition
        if let Some(line) = lines.get(start_line) {
            formatted_output.push_str(&format!("│{}\n", line.trim()));
        }

        last_line = start_line as i32;
    }

    if formatted_output.is_empty() {
        None
    } else {
        Some(formatted_output)
    }
}

fn separate_files(all_files: Vec<PathBuf>) -> (Vec<PathBuf>, Vec<PathBuf>) {
    let extensions = [
        "js", "jsx", "ts", "tsx", "py", "rs", "go", "c", "h", "cpp", "hpp", "cs", "rb", "java",
        "php", "swift",
    ];

    let mut files_to_parse = Vec::new();
    let mut remaining_files = Vec::new();

    for file in all_files {
        if let Some(ext) = file.extension().and_then(|e| e.to_str()) {
            if extensions.contains(&ext.to_lowercase().as_str()) {
                files_to_parse.push(file);
            } else {
                remaining_files.push(file);
            }
        } else {
            remaining_files.push(file);
        }
    }

    // Limit to 50 files max
    files_to_parse.truncate(50);

    (files_to_parse, remaining_files)
}

/// Load and parse source code files in the directory
pub fn parse_source_code_for_definitions(dir_path: &Path) -> Result<String> {
    if !dir_path.exists() {
        return Err(Error::DirectoryAccess(
            "This directory does not exist or you do not have permission to access it.".into(),
        ));
    }

    let extensions_to_languages =
        HashMap::from([("rs", "rust"), ("js", "javascript"), ("py", "python")]);

    let queries = load_queries();

    // Get all files at top level
    let all_files: Vec<PathBuf> = fs::read_dir(dir_path)
        .map_err(Error::DirectoryRead)?
        .filter_map(|entry| entry.ok().map(|e| e.path()))
        .collect();

    // Separate files to parse and remaining files
    let (files_to_parse, _remaining_files) = separate_files(all_files);

    let mut parsers: HashMap<&str, (Parser, Query)> = HashMap::new();
    let mut result = String::new();

    for file in files_to_parse {
        if let Some(ext) = file.extension().and_then(|e| e.to_str()) {
            if let Some(&lang_name) = extensions_to_languages.get(ext.to_lowercase().as_str()) {
                if !parsers.contains_key(lang_name) {
                    let language = load_language_parser(lang_name)?;
                    let mut parser = Parser::new();
                    parser
                        .set_language(language)
                        .map_err(|e| Error::LanguageError(e.to_string()))?;
                    let query = Query::new(language, queries[lang_name])
                        .map_err(|e| Error::QueryError(e.to_string()))?;
                    parsers.insert(lang_name, (parser, query));
                }

                if let Some((parser, query)) = parsers.get_mut(lang_name) {
                    if let Some(file_output) = parse_file(&file, parser, query) {
                        if !result.is_empty() {
                            result.push_str("|----\n");
                        }
                        result.push_str(&format!(
                            "{}\n",
                            file.strip_prefix(dir_path).unwrap().display()
                        ));
                        result.push_str(&file_output);
                    }
                }
            }
        }
    }

    if result.is_empty() {
        Ok("No source code definitions found.".into())
    } else {
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use insta::assert_snapshot;
    use std::fs::{self, File};
    use std::io::Write;
    use tempfile::TempDir;

    #[test]
    fn test_invalid_directory() {
        let result = parse_source_code_for_definitions(Path::new("/nonexistent/path"));
        assert!(matches!(result, Err(Error::DirectoryAccess(_))));
    }

    #[test]
    fn test_empty_directory() {
        let temp_dir = TempDir::new().unwrap();
        let result = parse_source_code_for_definitions(temp_dir.path()).unwrap();
        assert_snapshot!(result);
    }

    #[test]
    fn test_unsupported_files() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        fs::write(file_path, "Some content").unwrap();

        let result = parse_source_code_for_definitions(temp_dir.path()).unwrap();
        assert_snapshot!(result);
    }

    #[test]
    fn test_rust_definitions() {
        let temp_dir = TempDir::new().unwrap();
        let rust_content = r#"
                                    struct User {
                                        name: String,
                                        age: u32,
                                    }

                                    fn calculate_age(birth_year: u32) -> u32 {
                                        2024 - birth_year
                                    }

                                    impl User {
                                        fn new(name: String, age: u32) -> Self {
                                            User { name, age }
                                        }
                                    }
                                    "#;
        let file_path = temp_dir.path().join("test.rs");
        fs::write(&file_path, rust_content).unwrap();

        let result = parse_source_code_for_definitions(temp_dir.path()).unwrap();
        assert_snapshot!(result);
    }

    #[test]
    fn test_javascript_definitions() {
        let temp_dir = TempDir::new().unwrap();
        let js_content = r#"
            function calculateTotal(items) {
                return items.reduce((sum, item) => sum + item.price, 0);
            }

            function formatPrice(price) {
                return `$${price.toFixed(2)}`;
            }
            "#;
        let file_path = temp_dir.path().join("test.js");
        fs::write(&file_path, js_content).unwrap();

        let result = parse_source_code_for_definitions(temp_dir.path()).unwrap();
        assert_snapshot!(result);
    }

    #[test]
    fn test_multiple_file_types() {
        let temp_dir = TempDir::new().unwrap();

        // Create Rust file
        let rust_content = "fn test_function() {}";
        let rust_path = temp_dir.path().join("test.rs");
        fs::write(&rust_path, rust_content).unwrap();

        // Create JavaScript file
        let js_content = "function jsFunction() {}";
        let js_path = temp_dir.path().join("test.js");
        fs::write(&js_path, js_content).unwrap();

        // Create unsupported file
        fs::write(temp_dir.path().join("test.txt"), "plain text").unwrap();

        let result = parse_source_code_for_definitions(temp_dir.path()).unwrap();
        assert_snapshot!(result);
    }

    #[test]
    fn test_unreadable_file() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.rs");

        // Create a file with no read permissions
        {
            let mut file = File::create(&file_path).unwrap();
            file.write_all(b"fn test() {}").unwrap();
        }

        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mut perms = fs::metadata(&file_path).unwrap().permissions();
            perms.set_mode(0o000);
            fs::set_permissions(&file_path, perms).unwrap();
        }

        let result = parse_source_code_for_definitions(temp_dir.path()).unwrap();
        assert_snapshot!(result);
    }
}
