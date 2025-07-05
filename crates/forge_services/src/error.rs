use std::path::PathBuf;

use thiserror::Error;

/// Specialized error type for forge_services crate
#[derive(Error, Debug)]
pub enum ForgeServicesError {
    // File system errors
    #[error("File not found: {path}")]
    FileNotFound { path: PathBuf },

    #[error("Failed to read file: {path} - {error}")]
    FileReadError { path: String, error: String },

    #[error("Failed to write file: {path}")]
    FileWriteError { path: PathBuf, source: std::io::Error },

    #[error("Failed to create directories: {path}")]
    DirectoryCreationError { path: PathBuf, source: std::io::Error },

    #[error("Failed to remove file: {path}")]
    FileRemovalError { path: PathBuf, source: std::io::Error },

    #[error("Invalid UTF-8 in file: {path}")]
    InvalidUtf8 { path: PathBuf, source: std::string::FromUtf8Error },

    #[error("File size ({size} bytes) exceeds the maximum allowed size of {max_size} bytes")]
    FileTooLarge { path: String, size: u64, max_size: u64 },

    #[error("File size exceeds maximum allowed size: {size} bytes (max: {max_size} bytes)")]
    FileSizeExceeded { size: u64, max_size: u64 },

    #[error("Cannot overwrite existing file: overwrite flag not set")]
    FileOverwriteNotAllowed,

    // Path validation errors
    #[error("Path must be absolute. Please provide an absolute path starting with '/' (Unix) or 'C:\\' (Windows)")]
    PathNotAbsolute,

    // Command execution errors
    #[error("Command string is empty or contains only whitespace")]
    EmptyCommand,

    #[error("Command execution failed")]
    CommandExecutionFailed { source: std::io::Error },

    // HTTP and network errors
    #[error("Failed to fetch URL {url}: {error}")]
    HttpRequestFailed { url: String, error: String },

    #[error("HTTP status {status_code} for URL {url}")]
    HttpStatusError { url: String, status_code: u16 },

    #[error("Failed to read response content from {url}: {error}")]
    HttpContentReadError { url: String, error: String },

    #[error("Failed to fetch URL {url}")]
    HttpFetchError { url: String, source: reqwest::Error },

    #[error("Failed to read response content from {url}")]
    HttpResponseReadError { url: String, source: reqwest::Error },

    #[error("URL parse error: {url} - {error}")]
    UrlParseError { url: String, error: String },

    #[error("Robots.txt disallows access to {url}")]
    RobotsTxtDisallowed { url: String },

    // Authentication errors
    #[error("Failed to initialize auth")]
    AuthInitializationFailed,

    #[error("HTTP {status}: Authentication failed")]
    AuthenticationFailed { status: u16 },

    // Serialization/deserialization errors
    #[error("JSON serialization error")]
    JsonSerializationError { source: serde_json::Error },

    #[error("JSON deserialization error")]
    JsonDeserializationError { source: serde_json::Error },

    #[error("YAML serialization error")]
    YamlSerializationError { source: serde_yml::Error },

    #[error("YAML deserialization error")]
    YamlDeserializationError { source: serde_yml::Error },

    // Template errors
    #[error("Template compilation error for {name}")]
    TemplateCompilationError { name: String, source: handlebars::TemplateError },

    #[error("Template rendering error")]
    TemplateRenderingError { source: handlebars::RenderError },

    // MCP (Model Context Protocol) errors
    #[error("MCP client error")]
    McpClientError { source: Box<dyn std::error::Error + Send + Sync> },

    #[error("MCP server connection error")]
    McpServerConnectionError { source: Box<dyn std::error::Error + Send + Sync> },

    // Walker/search errors
    #[error("File walking error")]
    WalkerError { source: Box<dyn std::error::Error + Send + Sync> },

    #[error("Search pattern error")]
    SearchPatternError { source: Box<dyn std::error::Error + Send + Sync> },

    #[error("Glob pattern error")]
    GlobPatternError { source: glob::PatternError },

    // Snapshot errors
    #[error("Snapshot creation error for {path}")]
    SnapshotCreationError { path: PathBuf, source: Box<dyn std::error::Error + Send + Sync> },

    #[error("Snapshot restoration error for {path}")]
    SnapshotRestorationError { path: PathBuf, source: Box<dyn std::error::Error + Send + Sync> },

    // User interaction errors
    #[error("User prompt error")]
    UserPromptError { source: Box<dyn std::error::Error + Send + Sync> },

    #[error("No options provided")]
    NoOptionsProvided,

    // Forge app errors
    #[error("Forge app error: {0}")]
    ForgeAppError(#[from] forge_app::Error),

    // Generic errors for cases that don't fit specific categories
    #[error("Internal error: {message}")]
    Internal { message: String },

    #[error("External error")]
    External { source: Box<dyn std::error::Error + Send + Sync> },

    // Anyhow error for infrastructure compatibility
    #[error("Anyhow error: {0}")]
    AnyhowError(#[from] anyhow::Error),
}

/// Result type alias for forge_services operations
pub type Result<T> = std::result::Result<T, ForgeServicesError>;

impl ForgeServicesError {
    /// Create a new internal error with a custom message
    pub fn internal(message: impl Into<String>) -> Self {
        Self::Internal { message: message.into() }
    }

    /// Create a new external error from any error type
    pub fn external(error: impl std::error::Error + Send + Sync + 'static) -> Self {
        Self::External { source: Box::new(error) }
    }
}

// Conversion implementations for common error types
impl From<std::io::Error> for ForgeServicesError {
    fn from(error: std::io::Error) -> Self {
        Self::External { source: Box::new(error) }
    }
}

impl From<serde_json::Error> for ForgeServicesError {
    fn from(error: serde_json::Error) -> Self {
        Self::JsonDeserializationError { source: error }
    }
}

impl From<serde_yml::Error> for ForgeServicesError {
    fn from(error: serde_yml::Error) -> Self {
        Self::YamlDeserializationError { source: error }
    }
}

impl From<reqwest::Error> for ForgeServicesError {
    fn from(error: reqwest::Error) -> Self {
        Self::External { source: Box::new(error) }
    }
}

impl From<handlebars::TemplateError> for ForgeServicesError {
    fn from(error: handlebars::TemplateError) -> Self {
        Self::External { source: Box::new(error) }
    }
}

impl From<handlebars::RenderError> for ForgeServicesError {
    fn from(error: handlebars::RenderError) -> Self {
        Self::TemplateRenderingError { source: error }
    }
}

impl From<glob::PatternError> for ForgeServicesError {
    fn from(error: glob::PatternError) -> Self {
        Self::GlobPatternError { source: error }
    }
}

impl From<std::path::StripPrefixError> for ForgeServicesError {
    fn from(error: std::path::StripPrefixError) -> Self {
        Self::External { source: Box::new(error) }
    }
}

// Removed conflicting From implementation - anyhow provides a blanket implementation
// for any type that implements std::error::Error