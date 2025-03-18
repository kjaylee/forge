# Forge Merger

A utility library crate for the Forge project that merges all non-ignored files in a directory into a single string. Each file's content is preceded by its full path enclosed in separators.

## Features

- Recursively scans directories using `forge_walker`
- Skips binary files and only processes text files
- Each file's content is preceded by its full path enclosed in separators
- Customizable separator (default: `================`)

## Usage

### Basic Usage

```rust
use forge_merger::Merger;
use anyhow::Result;
use tokio::fs;

async fn merge_files() -> Result<()> {
    // Create a new merger instance
    let merger = Merger::new("/path/to/directory");
    
    // Process all files and get merged content as a string
    let merged_content = merger.process().await?;
    
    // Optionally write the merged content to a file
    fs::write("/path/to/output.txt", merged_content).await?;
    
    Ok(())
}
```

### Using Custom Separator

```rust
use forge_merger::Merger;
use anyhow::Result;
use tokio::fs;

async fn merge_files() -> Result<()> {
    // Create a merger with a custom separator
    let merger = Merger::new("/path/to/directory")
        .with_separator("-------------------");
    
    // Process all files and get merged content
    let merged_content = merger.process().await?;
    
    // Optionally write the merged content to a file
    fs::write("/path/to/output.txt", merged_content).await?;
    
    Ok(())
}
```

## Output Format

The merged content will have the following format:

```
================
File: /full/path/to/file1.txt
================
Content of file1.txt

================
File: /full/path/to/file2.txt
================
Content of file2.txt

... and so on
```