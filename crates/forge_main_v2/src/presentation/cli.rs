use std::path::PathBuf;

use clap::Parser;

#[derive(Parser, Debug)]
pub struct Cli {
    /// Run Forge with restricted access (no system access)
    #[arg(long)]
    pub restricted: bool,

    /// Directly process this prompt without entering interactive mode
    #[arg(short, long)]
    pub prompt: Option<String>,

    /// Read command from a file
    #[arg(short, long)]
    pub command: Option<PathBuf>,

    /// Dispatch an event directly (JSON format)
    #[arg(short, long)]
    pub event: Option<String>,

    /// Specify a custom workflow file
    #[arg(short, long)]
    pub workflow: Option<String>,

    /// Enable verbose mode to show tool execution details
    #[arg(short, long)]
    pub verbose: bool,
}
