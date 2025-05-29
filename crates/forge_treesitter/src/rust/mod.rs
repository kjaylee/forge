use std::fmt::Display;
use std::path::PathBuf;

/// Represents the type of code block captured
#[derive(Debug, Clone, PartialEq)]
pub enum Kind {
    Function,
    Struct,
    Enum,
    Constant,
}

impl Display for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Kind::Function => write!(f, "function"),
            Kind::Struct => write!(f, "struct"),
            Kind::Enum => write!(f, "enum"),
            Kind::Constant => write!(f, "constant"),
        }
    }
}

impl TryFrom<&str> for Kind {
    type Error = anyhow::Error;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "struct.definition" => Ok(Kind::Struct),
            "enum.definition" => Ok(Kind::Enum),
            "function.definition" => Ok(Kind::Function),
            "const.definition" => Ok(Kind::Constant),
            _ => Err(anyhow::anyhow!("Unsupported pattern found '{}'", value)),
        }
    }
}

/// Represents a captured code block with metadata
#[derive(Debug, Clone, PartialEq)]
pub struct Block {
    /// what type of snippet captured
    pub kind: Kind,
    /// code file path
    pub path: PathBuf,
    /// code snippet
    pub snippet: String,
    /// Char offset of snippet
    pub offset: Offset,
}

impl Block {
    pub fn hash(&self) -> String {
        use blake3::Hasher as Blake3;
        let mut hasher = Blake3::new();
        hasher.update(self.path.display().to_string().as_bytes());
        hasher.update(self.snippet.as_bytes());
        let hash = hasher.finalize();
        hash.to_hex().to_string()
    }

    /// converts absolute path to relative path based on cwd.
    pub fn relative_path(&self) -> PathBuf {
        let current_dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        pathdiff::diff_paths(&self.path, &current_dir).unwrap_or_else(|| self.path.clone())
    }
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct Offset {
    pub start: usize,
    pub end: usize,
}

impl Block {
    /// Create a new code block
    pub fn new(kind: Kind, path: PathBuf, snippet: String, offset: Offset) -> Self {
        Self { kind, path, snippet, offset }
    }
}
