use std::path::Path;

use tree_sitter::{Language, Parser};

pub fn get_language_by_extension(ext: &str) -> Option<Language> {
    match ext.to_lowercase().as_str() {
        "rs" => Some(tree_sitter_rust::LANGUAGE.into()),
        "js" | "jsx" | "ts" | "tsx" => Some(tree_sitter_javascript::LANGUAGE.into()),
        "py" => Some(tree_sitter_python::LANGUAGE.into()),
        _ => None,
    }
}

pub fn validate_parse(path: impl AsRef<Path>, content: &str) -> Result<(), String> {
    let path = path.as_ref();
    
    // Get file extension
    let ext = path
        .extension()
        .and_then(|e| e.to_str())
        .ok_or_else(|| "File has no extension".to_string())?;

    // Get language for the extension
    let language = if let Some(lang) = get_language_by_extension(ext) {
        lang
    } else {
        // If we don't support the language, consider it valid
        return Ok(());
    };

    // Initialize parser
    let mut parser = Parser::new();
    parser.set_language(&language).map_err(|e| e.to_string())?;

    // Try parsing the content
    let tree = parser
        .parse(content, None)
        .ok_or_else(|| format!("Failed to parse {} as {}", path.display(), ext))?;

    // Find syntax errors in the tree
    let root_node = tree.root_node();
    if root_node.has_error() || root_node.is_error() {
        let error_text = root_node.utf8_text(content.as_bytes())
            .unwrap_or("unknown error")
            .to_string();
        return Err(format!("Syntax error found in {} while parsing as {}: {}", 
            path.display(), ext, error_text));
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[test]
    fn test_rust_valid() {
        let content = r#"
fn main() {
    println!("Hello, world!");
}
"#;
        let path = PathBuf::from("test.rs");
        assert!(validate_parse(&path, content).is_ok());
    }

    #[test]
    fn test_rust_invalid() {
        let content = r#"
fn main() {
    println!("Hello, world!"
}
"#;
        let path = PathBuf::from("test.rs");
        assert!(validate_parse(&path, content).is_err());
    }

    #[test]
    fn test_javascript_valid() {
        let content = r#"
function hello() {
    console.log("Hello, world!");
}
"#;
        let path = PathBuf::from("test.js");
        assert!(validate_parse(&path, content).is_ok());
    }

    #[test]
    fn test_javascript_invalid() {
        let content = r#"
function hello() {
    console.log("Hello, world!"
}
"#;
        let path = PathBuf::from("test.js");
        assert!(validate_parse(&path, content).is_err());
    }

    #[test]
    fn test_python_valid() {
        let content = r#"
def hello():
    print("Hello, world!")
"#;
        let path = PathBuf::from("test.py");
        assert!(validate_parse(&path, content).is_ok());
    }

    #[test]
    fn test_python_invalid() {
        let content = r#"
def hello()
    print("Hello, world!")
"#;
        let path = PathBuf::from("test.py");
        assert!(validate_parse(&path, content).is_err());
    }

    #[test]
    fn test_unsupported_extension() {
        let content = "Some random content";
        let path = PathBuf::from("test.txt");
        assert!(validate_parse(&path, content).is_ok());
    }

    #[test]
    fn test_no_extension() {
        let content = "Some random content";
        let path = PathBuf::from("test");
        assert!(validate_parse(&path, content).is_err());
    }
}