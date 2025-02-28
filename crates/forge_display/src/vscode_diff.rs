//! VS Code Diff Viewer Integration
//!
//! This module provides functionality to display file changes in VS Code's diff viewer
//! with real-time streaming updates and line-by-line animations. It enables visualizing
//! changes as they happen, making it easier to understand complex file transformations.
//!
//! # Features
//!
//! * Real-time streaming updates to VS Code's diff viewer
//! * Line-by-line animated changes for better visualization
//! * Configurable update frequency and animation speed
//! * Automatic temporary file management
//! * Threshold-based updates to minimize resource usage
//! 
//! # Examples
//! 
//! ```no_run
//! use forge_display::{create_streaming_diff_viewer, VsCodeDiffConfig};
//! use std::path::Path;
//! 
//! async fn example() -> anyhow::Result<()> {
//!     let file_path = Path::new("/path/to/file.txt");
//!     let original_content = "original content";
//!     
//!     // Create a streaming diff viewer with default configuration
//!     let mut viewer = create_streaming_diff_viewer(
//!         file_path,
//!         original_content,
//!         VsCodeDiffConfig::default()
//!     ).await?;
//!     
//!     // As the file is modified, update the diff view
//!     viewer.update("updated content").await?;
//!     
//!     // Finalize the diff view when done
//!     viewer.finalize("final content").await?;
//!     
//!     Ok(())
//! }
//! ```

use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

use anyhow::{Context, Result};
use similar::{ChangeTag, TextDiff};
use tempfile::Builder;
use tokio::fs;

/// Configuration for VS Code diff viewing
pub struct VsCodeDiffConfig {
    /// Whether to enable VS Code diff viewing
    pub enabled: bool,
    /// Whether to keep temporary files after showing diff
    pub keep_temp_files: bool,
    /// Update frequency in milliseconds (how often to refresh the diff view)
    pub update_frequency_ms: u64,
    /// Minimum changes to trigger an update (percentage of total content)
    pub min_change_percent: f64,
    /// Whether to use animated diff (line by line updates)
    pub animated_diff: bool,
    /// Animation delay in milliseconds between line updates
    pub animation_delay_ms: u64,
}

impl Default for VsCodeDiffConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            keep_temp_files: false,
            update_frequency_ms: 15,    // 100ms default refresh rate
            min_change_percent: 0.5,     // 0.5% content change threshold
            animated_diff: true,         // Enable animated diff by default
            animation_delay_ms: 10,     // 100ms delay between line updates
        }
    }
}

/// Manages streaming diffs in VS Code
pub struct StreamingDiffViewer {
    /// Path to the file being modified
    path: PathBuf,
    /// Path to the original content temporary file
    original_path: Option<PathBuf>,
    /// Last time the diff was updated
    last_update: Instant,
    /// Original content hash for change detection
    content_hash: u64,
    /// Config for VS Code diff viewing
    config: VsCodeDiffConfig,
    /// Total characters processed so far (reserved for future use)
    _chars_processed: usize,
    /// VS Code diff process status
    vs_code_running: bool,
    /// Original content as lines
    original_lines: Vec<String>,
    /// Current state of processed content
    current_lines: Vec<String>,
}

impl StreamingDiffViewer {
    /// Create a new streaming diff viewer
    pub async fn new(path: impl AsRef<Path>, original_content: &str, config: VsCodeDiffConfig) -> Result<Self> {
        let path = path.as_ref().to_path_buf();
        
        // Skip if disabled
        if !config.enabled {
            return Ok(Self {
                path,
                original_path: None,
                last_update: Instant::now(),
                content_hash: 0,
                config,
                _chars_processed: 0,
                vs_code_running: false,
                original_lines: Vec::new(),
                current_lines: Vec::new(),
            });
        }
        
        // Create temporary file for original content
        let original_path = create_temp_file_with_original_name(&path, ".original", original_content).await?;
        
        // Calculate hash of original content for change detection
        let content_hash = calculate_simple_hash(original_content);
        
        // Split original content into lines
        let original_lines: Vec<String> = original_content.lines().map(|s| s.to_string()).collect();
        
        Ok(Self {
            path,
            original_path: Some(original_path),
            last_update: Instant::now(),
            content_hash,
            config,
            _chars_processed: 0,
            vs_code_running: false,
            original_lines,
            current_lines: Vec::new(),
        })
    }
    
    /// Update the diff with the current content
    pub async fn update(&mut self, current_content: &str) -> Result<()> {
        // Skip if disabled or no original file
        if !self.config.enabled || self.original_path.is_none() {
            return Ok(());
        }
        
        // Check if it's time to update based on frequency
        let now = Instant::now();
        if now.duration_since(self.last_update) < Duration::from_millis(self.config.update_frequency_ms) {
            return Ok(());
        }
        
        if self.config.animated_diff {
            // Use animated (line-by-line) diff
            self.update_animated(current_content).await?;
        } else {
            // Use standard update method
            self.update_standard(current_content).await?;
        }
        
        // Update state
        self.last_update = now;
        self.vs_code_running = true;
        
        Ok(())
    }
    
    /// Update using standard method (non-animated)
    async fn update_standard(&mut self, current_content: &str) -> Result<()> {
        // Check if content has changed enough to warrant an update
        let new_hash = calculate_simple_hash(current_content);
        let content_change = if self.content_hash == 0 {
            100.0 // First update
        } else {
            // Approximate change percentage based on hash difference
            let hash_diff = (new_hash as i64 - self.content_hash as i64).abs() as u64;
            (hash_diff as f64 / self.content_hash as f64) * 100.0
        };
        
        // If change is below threshold, skip update
        if content_change < self.config.min_change_percent && self.vs_code_running {
            return Ok(());
        }
        
        // Update the modified file (it's already on disk, we don't need to do anything)
        
        // Launch or refresh VS Code diff view
        if let Some(original_path) = &self.original_path {
            self.launch_vs_code(original_path, &self.path, false).await?;
        }
        
        // Update state
        self.content_hash = new_hash;
        
        Ok(())
    }
    
    /// Update using animated method (line-by-line)
    async fn update_animated(&mut self, current_content: &str) -> Result<()> {
        // Get lines from the current content
        let new_lines: Vec<String> = current_content.lines().map(|s| s.to_string()).collect();
        
        // If this is the first update, initialize the current_lines
        if self.current_lines.is_empty() {
            self.current_lines = self.original_lines.clone();
        }
        
        // Create strings that live long enough
        let current_content_str = self.current_lines.join("\n");
        let new_content_str = new_lines.join("\n");
        
        // Create a diff between current state and target state
        let diff = TextDiff::from_lines(&current_content_str, &new_content_str);
        let ops = diff.grouped_ops(3);
        
        // No changes to animate
        if ops.is_empty() {
            return Ok(());
        }
        
        // For animation, we need a temporary copy of the original path
        let original_path = self.original_path.as_ref().ok_or_else(|| anyhow::anyhow!("No original path"))?;
        
        // Prepare an animated content file
        let animated_path = create_temp_file_with_original_name(&self.path, ".animated", &self.original_lines.join("\n")).await?;
        
        // Launch VS Code with the animated diff
        self.launch_vs_code_animated(original_path, &animated_path, false).await?;
        
        // Animate changes line by line
        for group in ops {
            for op in group {
                // Process each operation (hunk) in the diff
                for change in diff.iter_changes(&op) {
                    match change.tag() {
                        // Handle insertions
                        ChangeTag::Insert => {
                            if let Some(new_idx) = change.new_index() {
                                // For insertions and replacements, update the animated content
                                if new_idx < new_lines.len() {
                                    // Extend current_lines if needed
                                    while self.current_lines.len() <= new_idx {
                                        self.current_lines.push(String::new());
                                    }
                                    
                                    // Update the specific line
                                    self.current_lines[new_idx] = new_lines[new_idx].clone();
                                    
                                    // Write the updated content to the animated file
                                    fs::write(&animated_path, self.current_lines.join("\n")).await?;
                                    
                                    // Add a delay for animation effect
                                    tokio::time::sleep(Duration::from_millis(self.config.animation_delay_ms)).await;
                                }
                            }
                        },
                        // Handle deletions
                        ChangeTag::Delete => {
                            if let Some(old_idx) = change.old_index() {
                                // Remove the line or replace with empty
                                if old_idx < self.current_lines.len() {
                                    // Set it to empty instead of removing to maintain line numbers
                                    self.current_lines[old_idx] = String::new();
                                    
                                    // Write the updated content to the animated file
                                    fs::write(&animated_path, self.current_lines.join("\n")).await?;
                                    
                                    // Add a delay for animation effect
                                    tokio::time::sleep(Duration::from_millis(self.config.animation_delay_ms)).await;
                                }
                            }
                        },
                        _ => {}, // Equal, no change needed
                    }
                }
            }
        }
        
        // Final update - make sure we have the exact new content
        self.current_lines = new_lines;
        fs::write(&animated_path, self.current_lines.join("\n")).await?;
        
        // Update content hash
        self.content_hash = calculate_simple_hash(current_content);
        
        // Clean up the animated temporary file
        if !self.config.keep_temp_files {
            let _ = fs::remove_file(&animated_path).await;
        }
        
        Ok(())
    }
    
    /// Finalize the diff by showing the final version
    pub async fn finalize(&mut self, _final_content: &str) -> Result<()> {
        // Skip if disabled or no original file
        if !self.config.enabled || self.original_path.is_none() {
            return Ok(());
        }
        
        // Launch the final VS Code diff view
        if let Some(original_path) = &self.original_path {
            self.launch_vs_code(original_path, &self.path, true).await?;
        }
        
        Ok(())
    }
    
    /// Close and clean up resources
    pub async fn close(&mut self) -> Result<()> {
        // Remove temporary files if needed
        if let Some(original_path) = &self.original_path {
            if !self.config.keep_temp_files {
                if let Err(e) = fs::remove_file(original_path).await {
                    eprintln!("Warning: Could not remove temporary file: {}", e);
                }
            }
        }
        
        self.original_path = None;
        self.vs_code_running = false;
        
        Ok(())
    }
    
    /// Launch VS Code with the diff view
    async fn launch_vs_code(&self, original_path: &Path, modified_path: &Path, is_final: bool) -> Result<()> {
        let script_path = get_script_path()?;
        
        // Build the keep-temp argument
        let mut args = vec![
            original_path.to_string_lossy().to_string(),
            modified_path.to_string_lossy().to_string(),
        ];
        
        if self.config.keep_temp_files {
            args.push("--keep-temp".to_string());
        }
        
        if is_final {
            args.push("--final".to_string());
        }
        
        // Execute the VS Code diff script
        Command::new(&script_path)
            .args(&args)
            .spawn()
            .with_context(|| {
                format!(
                    "Failed to execute VS Code diff script: {}",
                    script_path.display()
                )
            })?;
        
        Ok(())
    }
    
    /// Launch VS Code with an animated diff view
    async fn launch_vs_code_animated(&self, original_path: &Path, animated_path: &Path, is_final: bool) -> Result<()> {
        // For animated diffs, we use the VS Code diff command directly
        // This gives us more control over the process
        
        let mut args = vec![
            "--reuse-window".to_string(),
            "--diff".to_string(),
            original_path.to_string_lossy().to_string(),
            animated_path.to_string_lossy().to_string(),
        ];
        
        // When it's the final diff, we add a title
        if is_final {
            args.push("--title".to_string());
            args.push(format!("{} - Final Changes", self.path.file_name().unwrap_or_default().to_string_lossy()));
        }
        
        // Execute VS Code directly
        Command::new("code")
            .args(&args)
            .spawn()
            .with_context(|| "Failed to execute VS Code for animated diff")?;
        
        Ok(())
    }
}

/// A simple non-cryptographic hash function for content changes
fn calculate_simple_hash(content: &str) -> u64 {
    let mut hash: u64 = 0;
    for (i, byte) in content.bytes().enumerate() {
        hash = hash.wrapping_add((byte as u64).wrapping_mul(i as u64 + 1));
    }
    hash
}

/// Creates a streaming VS Code diff viewer for the given file
///
/// # Parameters
///
/// * `path` - The path of the file being modified
/// * `original_content` - The original content before modifications
/// * `config` - Configuration options for VS Code diff display
///
/// # Returns
///
/// * `Result<StreamingDiffViewer>` - The diff viewer object or an error
pub async fn create_streaming_diff_viewer(
    path: impl AsRef<Path>,
    original_content: &str,
    config: VsCodeDiffConfig,
) -> Result<StreamingDiffViewer> {
    StreamingDiffViewer::new(path, original_content, config).await
}

/// Shows a diff in VS Code between the original and modified content
/// 
/// # Parameters
/// 
/// * `path` - The path of the file being modified
/// * `original_content` - The original content before modifications
/// * `modified_content` - The new content after modifications
/// * `config` - Configuration options for VS Code diff display
/// 
/// # Returns
/// 
/// * `Result<()>` - Success or an error if opening VS Code fails
/// 
/// # Notes
/// 
/// This function will create temporary files as needed and clean them up
/// when VS Code is done with them (unless keep_temp_files is enabled).
/// 
/// For streaming diffs, use create_streaming_diff_viewer instead.
pub async fn show_diff_in_vscode(
    path: impl AsRef<Path>,
    original_content: &str,
    modified_content: &str,
    config: &VsCodeDiffConfig,
) -> Result<()> {
    if !config.enabled {
        return Ok(());
    }

    let path = path.as_ref();
    
    // If the content is the same, no need to show a diff
    if original_content == modified_content {
        return Ok(());
    }

    // Create a temporary file for the original content
    let original_path = create_temp_file_with_original_name(path, ".original", original_content).await?;
    
    // Use the actual file path for the modified content since it's already written
    let modified_path = path.to_path_buf();
    
    // Build the keep-temp argument if needed
    let keep_temp_arg = if config.keep_temp_files { "--keep-temp" } else { "" };
    
    // Get the script path
    let script_path = get_script_path()?;
    
    // Execute the VS Code diff script
    Command::new(&script_path)
        .arg(&original_path)
        .arg(&modified_path)
        .arg(keep_temp_arg)
        .spawn()
        .with_context(|| {
            format!(
                "Failed to execute VS Code diff script: {}",
                script_path.display()
            )
        })?;
    
    Ok(())
}

/// Creates a temporary file with content, using the original filename as part of the temp name
/// 
/// # Parameters
/// 
/// * `original_path` - The path of the original file 
/// * `suffix` - A suffix to add to the temporary file name (e.g., ".original")
/// * `content` - The content to write to the temporary file
/// 
/// # Returns
/// 
/// * `Result<PathBuf>` - The path to the created temporary file, or an error
async fn create_temp_file_with_original_name(
    original_path: &Path,
    suffix: &str,
    content: &str,
) -> Result<PathBuf> {
    // Extract the file name
    let file_name = original_path
        .file_name()
        .unwrap_or_default()
        .to_string_lossy();
    
    // Extract the extension if any
    let extension = original_path
        .extension()
        .map(|e| format!(".{}", e.to_string_lossy()))
        .unwrap_or_default();
    
    // Create a temp directory to hold our files (this has random chars, but that's ok)
    let temp_dir = tempfile::Builder::new()
        .prefix("forge-diff-")
        .tempdir()
        .context("Failed to create temporary directory")?;
    
    // Create a clean filename without random characters
    let clean_filename = format!("forge-{}{}{}", file_name, suffix, extension);
    let temp_path = temp_dir.path().join(&clean_filename);
    
    // Write content to the temporary file
    fs::write(&temp_path, content)
        .await
        .with_context(|| format!("Failed to write to temporary file: {}", temp_path.display()))?;
    
    // Keep the directory around (don't clean it up automatically)
    temp_dir.into_path();
    
    Ok(temp_path)
}

/// Gets the path to the VS Code diff script
/// 
/// # Returns
/// 
/// * `Result<PathBuf>` - The path to the VS Code diff script, or an error if not found
/// 
/// # Notes
/// 
/// This function first looks for the script in the standard executable directory,
/// then falls back to the development project path if needed.
fn get_script_path() -> Result<PathBuf> {
    // Try to get the executable path
    let exe_path = env::current_exe().context("Failed to get executable path")?;
    let exe_dir = exe_path.parent().context("Failed to get executable directory")?;
    
    // Look for the script in the same directory as the executable
    let script_path = exe_dir.join("scripts").join("vscode-diff.sh");
    
    if script_path.exists() {
        return Ok(script_path);
    }
    
    // Look for the script in the project root (for development)
    let project_script_path = PathBuf::from("/Users/amit/code-forge/scripts/vscode-diff.sh");
    
    if project_script_path.exists() {
        return Ok(project_script_path);
    }
    
    anyhow::bail!("VS Code diff script not found")
}