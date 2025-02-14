use std::fs;
use std::path::PathBuf;

use clap::Parser;

const DEFAULT_WORKFLOW: &str = "templates/workflows/default.toml";

#[derive(Parser)]
#[command(version = env!("CARGO_PKG_VERSION"))]
pub struct Cli {
    /// Path to a file containing initial commands to execute.
    ///
    /// The application will execute the commands from this file first,
    /// then continue in interactive mode.
    #[arg(long, short = 'c')]
    pub command: Option<String>,

    /// Direct prompt to process without entering interactive mode.
    ///
    /// Allows running a single command directly from the command line.
    #[arg(long, short = 'p')]
    pub prompt: Option<String>,

    /// Enable verbose output mode.
    ///
    /// When enabled, shows additional debugging information and tool execution
    /// details.
    #[arg(long, default_value_t = false)]
    pub verbose: bool,

    /// Enable restricted shell mode for enhanced security.
    ///
    /// Controls the shell execution environment:
    /// - Default (false): Uses standard shells (bash on Unix/Mac, cmd on
    ///   Windows)
    /// - Restricted (true): Uses restricted shell (rbash) with limited
    ///   capabilities
    ///
    /// The restricted mode provides additional security by preventing:
    /// - Changing directories
    /// - Setting/modifying environment variables
    /// - Executing commands with absolute paths
    /// - Modifying shell options
    #[arg(long, default_value_t = false, short = 'r')]
    pub restricted: bool,

    /// Path to a file containing the workflow to execute.
    #[arg(long, short = 'w', value_parser = path_parser, default_value = DEFAULT_WORKFLOW)]
    pub workflow: PathBuf,
}

/// Parses a path string into a `PathBuf` and validates it. if provided path is
/// relative then it will be resolved to the current working directory.
fn path_parser(path: &str) -> Result<PathBuf, String> {
    let mut path_buf = PathBuf::from(path);

    // Resolve relative paths to the current working directory.
    if path_buf.is_relative() {
        let cwd = std::env::current_dir().map_err(|e| e.to_string())?;
        path_buf = cwd.join(path_buf);
    }

    if !path_buf.exists() {
        return Err(format!("Path does not exist: '{}'", path_buf.display()));
    }

    if !path_buf.is_file() {
        return Err(format!("Path is not a file: '{}'", path_buf.display()));
    }

    if fs::metadata(&path_buf).is_err() {
        return Err(format!(
            "Unable to read file from path '{}'",
            path_buf.display()
        ));
    }

    Ok(path_buf)
}
