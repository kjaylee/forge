use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use tree_sitter::{Language, Parser, Query, QueryCursor};

fn load_language_parser(language_name: &str) -> Language {
    match language_name {
        "rust" => tree_sitter_rust::language(),
        "javascript" => tree_sitter_javascript::language(),
        "python" => tree_sitter_python::language(),
        _ => panic!("Unsupported language: {}", language_name),
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

/// Load and parse source code files in the directory
pub fn parse_source_code_for_definitions(dir_path: &Path) -> Result<String, String> {
    if !dir_path.exists() {
        return Err("This directory does not exist or you do not have permission to access it.".into());
    }

    let extensions_to_languages = HashMap::from([
        ("rs", "rust"),
        ("js", "javascript"),
        ("py", "python"),
    ]);

    let mut result = String::new();
    let queries = load_queries();

    let files_to_parse: Vec<PathBuf> = fs::read_dir(dir_path)
        .map_err(|_| "Failed to read directory.")?
        .filter_map(|entry| {
            let path = entry.ok()?.path();
            let ext = path.extension()?.to_str()?.to_lowercase();
            if extensions_to_languages.contains_key(ext.as_str()) {
                Some(path)
            } else {
                None
            }
        })
        .collect();

    let mut parsers: HashMap<&str, (Parser, Query)> = HashMap::new();

    for file in files_to_parse {
        if let Some(ext) = file.extension().and_then(|e| e.to_str()) {
            if let Some(&lang_name) = extensions_to_languages.get(ext) {
                if !parsers.contains_key(lang_name) {
                    let language = load_language_parser(lang_name);
                    let mut parser = Parser::new();
                    parser.set_language(language).expect("Failed to set language.");
                    let query = Query::new(language, queries[lang_name]).expect("Failed to load query.");
                    parsers.insert(lang_name, (parser, query));
                }

                if let Some((parser, query)) = parsers.get_mut(lang_name) {
                    match fs::read_to_string(&file) {
                        Ok(content) => {
                            if let Some(tree) = parser.parse(&content, None) {
                                let mut cursor = QueryCursor::new();
                                let captures = cursor.matches(query, tree.root_node(), content.as_bytes());
                                let mut formatted_output = String::new();
                                for m in captures {
                                    for c in m.captures {
                                        let node = c.node;
                                        formatted_output.push_str(&format!(
                                            "│ {}: {}\n",
                                            node.start_position().row + 1,
                                            node.utf8_text(content.as_bytes()).unwrap_or("")
                                        ));
                                    }
                                }
                                if !formatted_output.is_empty() {
                                    result.push_str(&format!(
                                        "|----\nFile: {}\n{}\n|----\n",
                                        file.display(),
                                        formatted_output
                                    ));
                                }
                            }
                        }
                        Err(_) => eprintln!("Failed to read file: {}", file.display()),
                    }
                }
            }
        }
    }

    Ok(if result.is_empty() {
        "No source code definitions found.".into()
    } else {
        result
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::{self, File};
    use std::io::Write;
    use tempfile::TempDir;

    #[test]
    fn test_invalid_directory() {
        let result = parse_source_code_for_definitions(Path::new("/nonexistent/path"));
        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err(),
            "This directory does not exist or you do not have permission to access it."
        );
    }

    #[test]
    fn test_empty_directory() {
        let temp_dir = TempDir::new().unwrap();
        let result = parse_source_code_for_definitions(temp_dir.path()).unwrap();
        assert_eq!(result, "No source code definitions found.");
    }

    #[test]
    fn test_unsupported_files() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        fs::write(file_path, "Some content").unwrap();
        
        let result = parse_source_code_for_definitions(temp_dir.path()).unwrap();
        assert_eq!(result, "No source code definitions found.");
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
        println!("{}", result);
        // Check for expected definitions
        assert!(result.contains("User"));
        assert!(result.contains("calculate_age"));
        assert!(result.contains("new"));
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
        println!("{}", result);
        
        // Check for expected definitions
        assert!(result.contains("calculateTotal"));
        assert!(result.contains("formatPrice"));
    }

    #[test]
    fn test_multiple_file_types() {
        let temp_dir = TempDir::new().unwrap();
        
        // Create Rust file
        let rust_content = "fn test_function() {}";
        fs::write(temp_dir.path().join("test.rs"), rust_content).unwrap();
        
        // Create JavaScript file
        let js_content = "function jsFunction() {}";
        fs::write(temp_dir.path().join("test.js"), js_content).unwrap();
        
        // Create unsupported file
        fs::write(temp_dir.path().join("test.txt"), "plain text").unwrap();

        let result = parse_source_code_for_definitions(temp_dir.path()).unwrap();
        
        // Check for expected definitions
        assert!(result.contains("test_function"));
        assert!(result.contains("jsFunction"));
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

        // The function should still work, just skip the unreadable file
        let result = parse_source_code_for_definitions(temp_dir.path()).unwrap();
        assert_eq!(result, "No source code definitions found.");
    }
}
