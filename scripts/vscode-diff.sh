#!/bin/bash
#
# vscode-diff.sh - Display file diffs in VS Code with advanced features
#
# This script manages the display of file differences in VS Code, providing
# several features not available through standard diff commands:
#
# - Visual differencing in VS Code with syntax highlighting
# - Smart window management to focus existing diff views
# - Support for animated diffs with line-by-line updates
# - Temporary file management with cleanup options
# - "Final" viewing mode for completed changes
#
# Usage: ./vscode-diff.sh <original_file> <modified_file> [--keep-temp] [--final]
#
# Arguments:
#   <original_file>   Path to the original file
#   <modified_file>   Path to the modified file
#   --keep-temp       Don't delete temporary files after showing diff
#   --final           Indicate this is the final version of the diff
#
# Requires VS Code to be installed and accessible via the 'code' command.
# This script is used by the Code Forge application to visualize changes.

# Exit on any error
set -e

ORIGINAL=$1
MODIFIED=$2
KEEP_TEMP=""
FINAL=""

# Parse additional arguments
for arg in "${@:3}"; do
    case $arg in
        --keep-temp)
            KEEP_TEMP="yes"
            ;;
        --final)
            FINAL="yes"
            ;;
    esac
done

# Validate arguments
if [ -z "$ORIGINAL" ] || [ -z "$MODIFIED" ]; then
    echo "Usage: $0 <original_file> <modified_file> [--keep-temp] [--final]"
    exit 1
fi

# Create readable names for the diff view
ORIGINAL_NAME=$(basename "$ORIGINAL")
MODIFIED_NAME=$(basename "$MODIFIED")

# Generate a unique identifier for this diff based on the file paths
# Using both paths ensures we detect changes in either original or modified files
DIFF_ID=$(echo "${ORIGINAL}:${MODIFIED}" | shasum | cut -d' ' -f1)

# Create a marker file with content to indicate this diff is already open
TEMP_DIR="${TMPDIR:-/tmp}"
MARKER_FILE="$TEMP_DIR/vscode_diff_${DIFF_ID}.marker"

# Store the process ID of the VS Code instance this script launches
WINDOW_ID=""

# Check if VS Code is already open with this diff
if [ -f "$MARKER_FILE" ]; then
    # Read the window ID stored in the marker file
    WINDOW_ID=$(cat "$MARKER_FILE" 2>/dev/null || echo "")
    
    # Check if the VS Code instance is still running
    if [ -n "$WINDOW_ID" ] && ps -p "$WINDOW_ID" > /dev/null; then
        # The window is still open - we'll focus it and then exit
        echo "Diff already open for $MODIFIED, focusing existing window..."
        
        # Send a request to macOS to activate the VS Code window
        if [ "$(uname)" == "Darwin" ]; then
            osascript -e 'tell application "Visual Studio Code" to activate' &>/dev/null || true
        elif [ -n "$(command -v xdotool)" ]; then
            # For Linux with xdotool installed
            xdotool search --name "Visual Studio Code" windowactivate || true
        fi
        
        # For the final diff, we still need to update the diff to show the latest content
        # This happens automatically because the files are being watched
        exit 0
    else
        # The window was closed, but marker file is still there
        echo "Previous diff window closed, opening new one..."
    fi
fi

# For debugging, log the files being diffed
if [ "$DEBUG" = "yes" ]; then
    echo "Diffing: $ORIGINAL vs $MODIFIED" > /tmp/forge-diff-debug.log
fi

# Launch VS Code and store the process ID
# We're using --reuse-window to maintain a single VS Code window for diffs if possible
code --reuse-window --diff "$ORIGINAL" "$MODIFIED" &
CODE_PID=$!

# Store the process ID in the marker file for future reference
echo "$CODE_PID" > "$MARKER_FILE"

# Do NOT clean up the marker file on exit in this case
# Instead, it should only be cleaned up when VS Code actually exits
# This allows us to detect if VS Code is still running with this diff

# If --keep-temp is not specified, and this is the final diff, clean up temporary files
if [ "$KEEP_TEMP" != "yes" ] && [ -n "$FINAL" ]; then
    # Wait a bit to make sure VS Code has opened the files
    sleep 1
    
    # If the original is a temporary file, remove it
    if [[ "$ORIGINAL" == *".original."* ]]; then
        rm -f "$ORIGINAL"
    fi
    
    # If the modified is a temporary file, remove it
    if [[ "$MODIFIED" == *".modified."* ]]; then
        rm -f "$MODIFIED"
    fi
fi
