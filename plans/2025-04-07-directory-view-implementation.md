# Directory View Implementation Plan

**Date:** 2025-04-07  
**Feature:** Project Directory View  
**Author:** Forge AI

## Objective

Implement a directory view panel in the Forge desktop application that displays the file structure of the current project. The directory view should be toggleable, resizable, and provide basic file/folder expand/collapse functionality with Lucide icons.

## Implementation Plan

### 1. Backend Implementation

#### 1.1 Add Directory Structure Command in `commands.rs`

Create a new command to fetch directory structure:

```rust
#[tauri::command]
pub async fn get_directory_structure(
    path: String,
    depth: Option<u32>,
    app_handle: AppHandle,
) -> Result<FileSystemEntry, String>
```

The `FileSystemEntry` struct will represent files and directories:

```rust
#[derive(Clone, Serialize)]
pub struct FileSystemEntry {
    pub name: String,
    pub path: String,
    pub is_directory: bool,
    pub children: Option<Vec<FileSystemEntry>>,
}
```

Implementation details:
- Traverse directories recursively up to specified depth
- Skip hidden files and directories
- Sort directories first, then files alphabetically
- Handle errors gracefully for inaccessible files/folders

#### 1.2 Register the Command

Add the new command to the Tauri builder in `main.rs`:

```rust
.invoke_handler(tauri::generate_handler![
    commands::get_directory_structure,
    // ...other existing commands
])
```

### 2. Frontend Implementation

#### 2.1 Create DirectoryStore

Create `src/stores/DirectoryStore.tsx` with Zustand:

State:
- `directoryTree`: File system structure
- `isLoading`: Loading state
- `isVisible`: Panel visibility toggle
- `panelWidth`: Panel width in pixels
- `expandedPaths`: Set of expanded directory paths
- `error`: Error message if any

Actions:
- `setDirectoryTree`
- `setLoading`
- `setVisible`/`toggleVisible`
- `setPanelWidth`
- `toggleExpandPath`/`setExpandedPath`
- `setError`

Operations:
- `loadDirectoryStructure`: Invoke backend command to fetch structure

Implement persistence for user preferences:
- Save panel visibility state
- Save panel width
- Store using Zustand persist middleware

#### 2.2 Create Directory View Components

##### 2.2.1 DirectoryView Component

Create `src/components/DirectoryView.tsx`:
- Main container for directory panel
- Header with "Project Files" title
- ScrollArea for directory content
- Loading/Error/Empty states
- Connect to DirectoryStore

##### 2.2.2 TreeItem Component

Create a recursive component for file/folder items:
- Display appropriate Lucide icon (Folder/FileText)
- Show expand/collapse indicators (ChevronRight/ChevronDown)
- Handle expand/collapse interactions
- Proper indentation for nested items
- Truncate long filenames

#### 2.3 Update App Layout

Modify `src/App.tsx`:

Add imports:
```tsx
import { useDirectoryStore } from '@/stores/DirectoryStore';
import DirectoryView from '@/components/DirectoryView';
import { PanelLeft } from 'lucide-react';
```

Update ChatInterface component:
- Add a resizable panel for directory view (conditionally rendered)
- Add toggle button in the main UI
- Adjust panel sizing calculations to include directory panel
- Connect to DirectoryStore for state management

### 3. Styling

#### 3.1 UI Styling with Tailwind

TreeItem styling:
```tsx
className={cn(
  "flex items-center py-1 px-2 hover:bg-accent/50 rounded-md cursor-pointer",
  "transition-colors duration-100 text-sm",
)}
```

Toggle button styling:
```tsx
className="p-2 mr-1 hover:bg-accent/50 rounded-md"
```

Use consistent colors:
- Folder icons: "text-blue-500"
- File icons: "text-gray-500"
- Muted elements: "text-muted-foreground"
- Active elements: "text-primary"

### 4. Testing and Verification

#### 4.1 Backend Testing
- Test with various directory structures
- Test error cases (non-existent paths, permission issues)
- Test performance with large directories

#### 4.2 Frontend Testing
- Verify state persistence
- Test expand/collapse functionality
- Test toggle and resize operations
- Test with long file names and deep hierarchies

#### 4.3 Edge Cases
- Empty directories
- Very deep nesting
- Special characters in filenames
- Very large directories

## Timeline

1. **Day 1**: Backend Implementation
   - Create the Rust backend command
   - Test with different directory structures

2. **Days 1-2**: Frontend Store & Data Layer
   - Implement DirectoryStore
   - Add persistence for user preferences

3. **Days 2-3**: UI Components
   - Create DirectoryView and TreeItem components
   - Implement styling

4. **Days 3-4**: Integration
   - Modify App.tsx to include directory panel
   - Implement toggle and resize functionality

5. **Days 4-5**: Testing & Optimization
   - Performance testing
   - Bug fixes and edge case handling

## Verification Criteria

The implementation is successful when:

1. The directory view accurately displays the project's file structure
2. Users can expand and collapse directories
3. The panel can be toggled on/off
4. The panel can be resized to the user's preference
5. The panel state (visibility and width) persists between sessions
6. The UI is responsive and performs well with large directories
7. Proper error handling is in place for edge cases

## Potential Risks and Mitigations

1. **Performance Issues with Large Directories**
   - Risk: Traversing and rendering large directories may cause performance issues
   - Mitigation: Implement depth limiting, lazy loading, and virtualization

2. **File System Access Errors**
   - Risk: Permission issues or other file system errors
   - Mitigation: Robust error handling and user feedback

3. **UI Layout Conflicts**
   - Risk: Adding a new panel may disrupt existing layout
   - Mitigation: Careful testing with various window sizes and content types

4. **Cross-Platform Compatibility**
   - Risk: Different file system behaviors across platforms
   - Mitigation: Test on all target platforms (Windows, macOS, Linux)