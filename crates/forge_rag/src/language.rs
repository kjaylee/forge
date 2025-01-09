#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Language {
    Rust,
    Python,
    JavaScript,
    TypeScript,
}

impl Language {
    pub fn get_file_extensions(&self) -> Vec<&str> {
        match self {
            Language::Rust => vec!["rs"],
            Language::Python => vec!["py"],
            Language::JavaScript => vec!["js", "jsx"],
            Language::TypeScript => vec!["ts", "tsx"],
        }
    }

    pub fn from_file_extension(ext: &str) -> Option<Self> {
        match ext {
            "rs" => Some(Language::Rust),
            "py" => Some(Language::Python),
            "js" | "jsx" => Some(Language::JavaScript),
            "ts" | "tsx" => Some(Language::TypeScript),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_language_file_extensions() {
        assert_eq!(Language::Rust.get_file_extensions(), vec!["rs"]);
        assert_eq!(Language::Python.get_file_extensions(), vec!["py"]);
        assert_eq!(Language::JavaScript.get_file_extensions(), vec!["js", "jsx"]);
        assert_eq!(Language::TypeScript.get_file_extensions(), vec!["ts", "tsx"]);
    }

    #[test]
    fn test_language_from_extension() {
        assert!(matches!(Language::from_file_extension("rs"), Some(Language::Rust)));
        assert!(matches!(Language::from_file_extension("py"), Some(Language::Python)));
        assert!(matches!(Language::from_file_extension("js"), Some(Language::JavaScript)));
        assert!(matches!(Language::from_file_extension("jsx"), Some(Language::JavaScript)));
        assert!(matches!(Language::from_file_extension("ts"), Some(Language::TypeScript)));
        assert!(matches!(Language::from_file_extension("tsx"), Some(Language::TypeScript)));
        assert!(Language::from_file_extension("unknown").is_none());
    }
}