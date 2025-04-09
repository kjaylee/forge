# Side-by-Side Diff Viewer for forge_desktop

## Objective

Enhance the forge_desktop application to display diffs in a GitHub-like side-by-side format when using patch and create tools. The implementation should include a file browser section showing changes (similar to VS Code), syntax highlighting, and a full-view modal for detailed inspection.

## Implementation Plan

### 1. Create a Side-by-Side Diff Component

Priority: High
Complexity: Medium
Dependencies: None

1. Create a new React component `SideBySideDiff.tsx` in the `forge_desktop/src/components/document` directory:

   - Implement a two-column layout for side-by-side diff display
   - Support syntax highlighting with line numbers
   - Highlight added/removed/modified lines with appropriate colors
   - Handle unchanged sections with context lines
   - Support collapsible sections for large diffs

2. Create helper utility functions in a new file `diffUtils.ts` to:
   - Parse the diff content from tool results
   - Convert unified diffs to side-by-side format
   - Extract file paths and other metadata from diff headers

### 2. Modify Diff Output Format in forge_display

Priority: Medium
Complexity: Medium
Dependencies: None

1. Enhance the `DiffFormat` struct in `forge_display/src/diff.rs` to:
   - Add an option to generate output in a structured JSON format that's easier to parse in the UI
   - Include metadata like file path, modification type, and hunks
   - Add tests for the new output format

### 3. Create a File Changes Browser Component

Priority: Medium
Complexity: High
Dependencies: #1

1. Create a new React component `FileChangesBrowser.tsx` in the `forge_desktop/src/components` directory:

   - Display a tree view of modified files (similar to VS Code's SCM view)
   - Group files by status (created, modified, deleted)
   - Show a summary of changes (+/- lines) for each file
   - Support collapsible folders and file groups
   - Allow clicking on files to view their diffs

2. Create a store or context to track file changes across sessions:
   - Add a new store `ChangesStore.tsx` to track modified files
   - Implement methods to update the store when new diffs are generated
   - Persist change information between sessions

### 4. Create a Full-View Diff Modal

Priority: Medium
Complexity: Medium
Dependencies: #1

1. Create a new React component `DiffModalView.tsx` in `forge_desktop/src/components`:
   - Implement a modal dialog that covers most of the screen
   - Display the side-by-side diff in full view with syntax highlighting
   - Add navigation controls for moving between files and hunks
   - Include a header showing file metadata and actions

### 5. Enhance Tool Result Display

Priority: High
Complexity: Medium
Dependencies: #1

1. Modify `ToolResultDisplay.tsx` to detect diff content from patch and create tools:

   - Add detection logic to identify diff output from specific tools
   - For diff content, show a preview with option to expand
   - Add a button to open the full diff view in the modal

2. Modify `messageUtils.ts` to extract and categorize diffs from tool results:
   - Add parsing logic to identify and categorize diff content
   - Extract file paths and other metadata from diff headers
   - Track changes across multiple tool invocations in a session

### 6. Update DocumentView and ConversationSection

Priority: Medium
Complexity: Low
Dependencies: #1, #3, #5

1. Enhance `DocumentView.tsx` to:

   - Add a panel or toggle to reveal the file changes browser
   - Update layout to accommodate the new components

2. Modify `ConversationSection.tsx` to:
   - Recognize and specially handle diff output
   - Integrate with the new diff viewer components

### 7. Add UI Integration and Polish

Priority: Low
Complexity: Medium
Dependencies: All previous steps

1. Add new UI components as needed:

   - Create custom badges or icons for different file states
   - Add toolbar buttons for diff-related actions
   - Implement keyboard shortcuts for navigating diffs

2. Improve visual styling:
   - Add consistent color coding for additions and deletions
   - Ensure dark mode compatibility
   - Add animations for expanding/collapsing diffs

## Verification Criteria

- The side-by-side diff viewer correctly displays changes with proper syntax highlighting
- File paths and metadata are correctly extracted and displayed
- The diff viewer works consistently for various programming languages
- The file changes browser correctly shows modified files
- Users can navigate between diffs and expand/collapse sections
- The full-view modal opens correctly and displays the diff with proper formatting
- All components work correctly in both light and dark modes
- Performance remains good even with large diffs

## Potential Risks and Mitigations

- Risk 1: Performance issues with large diffs
  Mitigation: Implement virtualized scrolling and lazy loading of diff content

- Risk 2: Compatibility issues with different programming languages
  Mitigation: Use a robust syntax highlighting library and test with various file types

- Risk 3: Complex diff parsing logic
  Mitigation: Write comprehensive tests for the diff parsing utilities

- Risk 4: UI complexity with nested components
  Mitigation: Maintain a clean component hierarchy and use proper state management

- Risk 5: Integration with existing tool output
  Mitigation: Carefully analyze current output format and ensure backward compatibility

## Alternative Approaches

1. **Enhanced Unified View**: Instead of a side-by-side view, enhance the existing unified view with better formatting, collapsible sections, and syntax highlighting. This would be simpler but less visually informative.

2. **External Diff Library**: Use an existing React diff viewer library like 'react-diff-viewer' instead of building a custom solution. This would be faster to implement but might have limitations for customization.

3. **WebWorker-based Diff Generation**: Move the diff generation logic to a web worker to prevent UI freezing with large diffs. This would add complexity but improve performance for large diffs.

4. **Server-Side Diff Rendering**: Generate the diff HTML on the Rust side and just display it in the UI. This would move complexity from the frontend to the backend.
