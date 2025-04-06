# Forge Desktop Project Directory Selection & Management

## Objective

Enhance the Forge desktop application with the ability to select and manage project directories, similar to GitHub Desktop. The application should:

1. Show a project selection screen on first launch instead of the chat interface
2. Only display the chat interface when a project/repository is selected
3. Persist the state of previously opened projects
4. Display a list of recent projects for easy access
5. Allow users to switch between projects directly from the chat screen
6. Enable users to add new projects without leaving the chat interface


## Implementation Plan

### 1. Backend Implementation (Rust)

#### 1.1. State Management Enhancements

Extend the `ForgeState` struct in `commands.rs` to track projects:

1. Create new data structures for project information
2. Add project-related state to `ForgeState`
3. Update state initialization to handle project-less startup

#### 1.2. Project Management Commands

Add the following Tauri commands to `commands.rs`:

1. `select_project`: Open a project directory and set as current
2. `get_current_project`: Get the active project path and info
3. `get_recent_projects`: Get the list of recently opened projects
4. `save_projects_state`: Save the project state to disk
5. `load_projects_state`: Load the project state from disk
6. `close_current_project`: Close the current project and return to project selection
7. `switch_project`: Switch to a different project from the recent projects list
8. `create_new_project`: Create or initialize a new project at the specified location

#### 1.3. Persistence Implementation

Create a new module for project persistence:

- Use the Tauri fs-extra plugin to handle file operations
- Store project data in the app's configuration directory
- Use a JSON format for storage
- Implement error handling and recovery mechanisms

#### 1.4. Workflow Integration

Modify the existing workflow loading and conversation initialization:

- Update `load_workflow` to consider the project path
- Enhance `init_conversation` to set project-related variables
- Allow workflows to access the current project information
- Add graceful conversation state saving when switching projects

### 2. Frontend Implementation (React/TypeScript)

#### 2.1. Application Structure Redesign

Restructure the main application flow to implement the GitHub Desktop-like experience:

1. Create a conditional rendering system based on project selection status
2. Implement two primary views:
   - Project Selection View (shown when no project is selected)
   - Chat Interface View (shown only when a project is selected)
3. Add a project navigation sidebar/dropdown in the chat interface

#### 2.2. Project Context

Create a new React Context (`ProjectContext.tsx`) to manage project state:

```typescript
interface ProjectInfo {
  path: string;
  name: string;
  lastAccessed: string;
}

interface ProjectContextType {
  currentProject: ProjectInfo | null;
  recentProjects: ProjectInfo[];
  isLoading: boolean;
  error: string | null;
  selectProject: (path?: string) => Promise<void>;
  switchProject: (projectInfo: ProjectInfo) => Promise<void>;
  createNewProject: (path: string, name?: string) => Promise<void>;
  closeProject: () => Promise<void>;
  refreshProjects: () => Promise<void>;
}
```

#### 2.3. Project Selection Screen

Create a new component `ProjectSelectionView.tsx` for the GitHub Desktop-like start screen:

1. Header with logo and application name
2. Recent Projects section
   - List of recent projects with name, path, and last accessed time
   - Click to open functionality
   - Option to remove from recent list
3. "Open Repository" button to browse for a repository
4. "Create New Repository" button with options for repository initialization
5. Help/documentation links

#### 2.4. UI Components

Create the following new components:

1. `ProjectCard.tsx`:
   - Displays a project item in the selection screen
   - Shows project name, path, and last accessed time
   - Includes hover effects and selection indicators
   
2. `ProjectHeader.tsx`:
   - Displays the current project name and path in the chat interface
   - Includes a dropdown to switch between recent projects
   - Contains buttons for project actions (close, add new, etc.)

3. `EmptyStateMessage.tsx`:
   - Shown when a project contains no files or when other empty states occur
   - Provides guidance on next steps

4. `DirectoryPicker.tsx`:
   - Dialog component for selecting a directory
   - Uses Tauri's dialog API
   - Provides feedback during directory scanning/loading

5. `ProjectSwitcher.tsx`:
   - Dropdown or sidebar component located in the chat interface
   - Lists all recent projects for quick switching
   - Includes option to add new project
   - Shows currently active project

6. `NewProjectDialog.tsx`:
   - Modal dialog for creating a new project
   - Options for project name, location, and initialization
   - Configuration options for project type (optional for future use)

#### 2.5. Modified App Component

Update the main `App.tsx` component to implement conditional rendering:

```typescript
function App() {
  const { currentProject, isLoading } = useProject();
  
  // Show loading spinner during initial load or project switching
  if (isLoading) {
    return <LoadingScreen />;
  }
  
  // Show project selection if no project is selected
  if (!currentProject) {
    return <ProjectSelectionView />;
  }
  
  // Show chat interface with project navigation when a project is selected
  return <ChatInterfaceWithProjectNavigation />;
}
```

#### 2.6. Navigation Between Projects

Implement smooth transitions between projects and workflows:

1. Add a project switcher dropdown in the conversation header
   - List all recent projects
   - Show currently active project
   - Include "Add New Project" option
   - Include "Back to Project Selection" option

2. Implement project switching functionality:
   - Save current conversation state when switching
   - Load project-specific conversation if one exists
   - Initialize new conversation if none exists for the project
   - Update UI to reflect the newly selected project

3. Add keyboard shortcuts for project navigation:
   - Ctrl+P/Cmd+P for project switcher popup
   - Alt+Left/Right to cycle through recent projects
   - Ctrl+N/Cmd+N to create new project

#### 2.7. In-Chat Project Management

Add functionality to manage projects directly from the chat interface:

1. "Add New Project" functionality:
   - Dialog accessible from the project switcher
   - Options for creating new or selecting existing directories
   - Automatic project initialization with appropriate defaults
   
2. Project settings panel:
   - Accessible from the project header
   - Options to rename, reconfigure, or remove projects
   - Project-specific settings (if applicable)

3. Quick project operations:
   - Context menu for common project tasks
   - Buttons for frequent operations

### 3. Integration & Data Flow

#### 3.1. Startup Sequence

1. App initialization
2. Load saved project state from local storage
3. Check if a project was previously active:
   - If yes, load it and show the chat interface
   - If no, show the project selection screen
4. Initialize UI based on current state

#### 3.2. Project Selection Flow

1. User selects a project from recent list or clicks "Open Repository"
2. If "Open Repository", app prompts for directory selection
3. Backend validates the selected directory is a valid project/repository
4. Current project state is updated
5. UI transitions from selection screen to chat interface
6. New conversation is initialized with project context

#### 3.3. Project Switching Flow

1. User selects a different project from the project switcher dropdown
2. Current conversation state is saved
3. New project is loaded and set as current
4. Project-specific conversation is loaded if exists, or new conversation is initialized
5. UI updates to reflect the newly selected project

#### 3.4. New Project Creation Flow

1. User selects "Add New Project" from project switcher
2. New project dialog appears with options
3. User provides project details and location
4. Backend initializes the new project
5. Project is added to recent projects and set as current
6. New conversation is initialized with the project context

#### 3.5. Project State Persistence

1. Project state is saved when:
   - A new project is selected
   - The application is closed
   - A project is closed to return to the selection screen
   - Switching between projects
   - Explicitly requested by the user
   
2. Project state is loaded:
   - On application startup
   - When switching between projects
   - When requested via refresh

### 4. ShadCN Component Usage

Implement all UI using ShadCN components exclusively:

1. Use `Card`, `CardHeader`, `CardContent` for project selection items
2. Implement project switcher using `DropdownMenu` and `DropdownMenuItem` components
3. Use `Dialog` for project creation and directory selection
4. Implement `Button` components with proper variants for different actions
5. Use `Separator` components to visually divide sections
6. Implement proper loading states with `Skeleton` components
7. Use `Typography` components for consistent text styling
8. Implement `Tabs` for project settings if needed
9. Use `Tooltip` for explaining functionality
10. Implement keyboard shortcuts with `CommandMenu` component

## Verification Criteria

The implementation will be considered successful when:

1. Users are presented with a project selection screen on first launch
2. The chat interface is only shown after a project is selected
3. Selected project information is correctly persisted between sessions
4. Users can successfully switch between projects from within the chat interface
5. Users can add new projects without returning to the project selection screen
6. Project switching preserves conversation state correctly
7. The UI transitions smoothly between projects
8. All existing functionalities work correctly within the new project context
9. The UI uses ShadCN components exclusively with a consistent design language
10. Edge cases are properly handled with user-friendly error messages
11. Performance impact is minimal, especially during startup and project switching

## Potential Risks and Mitigations

### 1. User Experience Disruption

**Risk**: The change from immediate chat to project selection first may confuse existing users
**Mitigation**:
- Add clear onboarding for first-time users after the update
- Provide visual cues and guidance in the project selection screen
- Consider a gradual rollout with optional opt-in for early versions

### 2. Performance With Large Repositories

**Risk**: Large project directories might cause scanning/loading delays
**Mitigation**: 
- Implement asynchronous loading with progress indicators
- Add background indexing with low priority
- Cache project structure information

### 3. Cross-Platform File Path Issues

**Risk**: File paths and permissions behave differently across operating systems
**Mitigation**:
- Use Tauri's platform-agnostic APIs
- Test thoroughly on all supported platforms
- Handle OS-specific edge cases with platform detection

### 4. Integration With Existing Workflows

**Risk**: Existing workflows might not be designed to be project-aware
**Mitigation**:
- Update all workflow definitions to be project-aware
- Add fallback mechanisms for workflows that don't need project context
- Create comprehensive tests to verify workflow behavior with/without projects

### 5. Conversation State Management During Project Switching

**Risk**: Switching between projects might cause conversation state loss or corruption
**Mitigation**:
- Implement robust state saving before project switches
- Add automatic recovery mechanisms
- Provide user warnings when switching from unsaved states