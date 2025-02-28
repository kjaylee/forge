# VS Code Diff Viewer Integration

This feature allows file changes from `fs_create` and `fs_patch` operations to be automatically displayed in the VS Code diff viewer with real-time streaming updates and line-by-line animations.

## Features

- Shows file changes in VS Code diff viewer after modifications
- Streams updates to the VS Code diff viewer in real-time with animated line-by-line changes
- Works with both `fs_create` and `fs_patch` operations
- Uses VS Code's built-in diff viewing capabilities
- Preserves file context and proper syntax highlighting
- Automatically cleans up temporary files
- Optimized to show changes only when they are significant
- Animates changes for better visualization of what's happening

## How It Works

When a file is modified through either `fs_create` or `fs_patch`:

1. The original file content is captured before modification
2. A streaming diff viewer is initialized that will update as the file is processed
3. As changes to the file are processed:
   - Each change is reflected in the terminal diff output line by line
   - With animated diff enabled, VS Code shows changes happening line by line
   - The VS Code diff viewer updates incrementally to show changes as they happen
   - Updates happen in real-time as the file is being processed
4. Once processing is complete:
   - A final diff view is shown with complete changes
   - Temporary files are cleaned up automatically

## Requirements

- VS Code must be installed and accessible in the PATH
- The `code` command must be available from the terminal

## Configuration

The feature can be configured through the `VsCodeDiffConfig` struct:

```rust
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
```

The streaming and animation behavior can be fine-tuned:
- `update_frequency_ms`: Controls how often VS Code updates (default: 100ms)
- `min_change_percent`: Sets the minimum content change percentage needed to trigger an update (default: 0.5%)
- `animated_diff`: Enables or disables the animated line-by-line diff (default: true)
- `animation_delay_ms`: Controls the speed of the animation (default: 100ms)

## Troubleshooting

If the diff viewer doesn't open:

1. Make sure VS Code is properly installed
2. Verify the `code` command is in your PATH
   - Run `code --help` in your terminal to check
3. Check permissions for creating temporary files
4. Look for error messages in the terminal output

## Technical Implementation

The system uses the VS Code CLI's diff command with two different approaches:

**Standard Mode:**
```
code --reuse-window --diff <original_file> <modified_file>
```

**Animated Mode:**
Creates a temporary file that's updated line by line with small delays to create an animation effect. This provides a visual experience similar to what you would see in advanced git clients or IDE extensions, showing exactly how the file changes over time rather than just the final result.

This ensures:
1. The diff opens in the existing VS Code window rather than creating a new one
2. The diff is displayed with full syntax highlighting and features
3. In animated mode, changes are shown line by line with smooth transitions
4. The user experience is more dynamic and provides better visual feedback
