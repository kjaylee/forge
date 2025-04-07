# Environment Refactor

## Objective

Refactor the `Environment` struct by removing `cwd` and `pid` fields, while ensuring all dependent parts of the codebase are updated to maintain functionality.

## Implementation Plan

## Detailed Implementation Notes

### Conversation Updates

- Add `pub cwd: PathBuf` field to the `Conversation` struct
- Update `Conversation::new()` constructor to take a `cwd: PathBuf` parameter and store it
- Add a `path()` or `cwd()` helper method to easily access the working directory

### API Method Changes

- Update the `init` method signature to: `async fn init(&self, path: PathBuf) -> anyhow::Result<ConversationId>`
- The method will look for a workflow configuration in the provided path
- If no workflow configuration exists, use the default workflow
- Use the provided path as the conversation's working directory

### Tool Implementation Updates

- Modify tool implementation to accept a reference to the `Conversation` as a parameter
- File system tools will directly access the conversation's `cwd` field via this reference
- This approach ensures tools always have access to the correct working directory context
- Consider updating the tool trait/interface to standardize this pattern across all tools
- Create a backwards compatibility layer for old persisted data that lacks the `cwd` field

### Changes

- For the scope of this refactoring, we'll focus only on the core functionality

1.  Modify `Environment` struct definition in `forge_domain/src/env.rs`
    - Remove `cwd` field
    - Remove `pid` field
    - Update any methods that directly reference these fields
    - Priority: High
    - Complexity: Low
    - Dependencies: None
2.  Update `Conversation` struct in `forge_domain/src/conversation.rs`
    - Add a new `cwd` field of type `PathBuf`
    - Modify the constructor to accept and store a `cwd` parameter
    - Consider adding helper methods to access the cwd if needed
    - Priority: High
    - Complexity: Low
    - Dependencies: Step 1
3.  Update the API trait in `forge_api/src/api.rs`
    - Modify the `init` method signature to accept only a `path` parameter: `async fn init(&self, path: PathBuf) -> anyhow::Result<ConversationId>`
    - Remove the workflow parameter as it will be loaded from the path
    - Update the method documentation to reflect the new behavior
    - Priority: High
    - Complexity: Medium
    - Dependencies: Steps 1-2
4.  Implement updated `init` method in `forge_api/src/forge_api.rs`
    - Modify implementation to load workflow from the provided path
    - Reuse existing workflow loading logic internally
    - Create a new conversation with the loaded workflow and the path
    - Priority: High
    - Complexity: Medium
    - Dependencies: Step 3
5.  Remove the `update_cwd` method from the `API` trait and its implementations
    - This is no longer needed as `cwd` will be conversation-specific
    - Priority: Medium
    - Complexity: Low
    - Dependencies: Steps 1-4
6.  Remove the `load` method from the `API` trait and its implementations
    - Incorporate this functionality into the updated `init` method
    - Priority: Medium
    - Complexity: Medium
    - Dependencies: Steps 3-4
7.  Update all references to `env.cwd` in the codebase
    - In `forge_services/src/template.rs` - Modify the template creation to use the conversation reference's `cwd` instead of env's cwd
    - In `forge_services/src/tools/fs/fs_write.rs` - Update tool implementation to access the conversation's `cwd` directly via reference
    - In `forge_services/src/tools/fs/fs_read.rs` - Modify to use the passed conversation reference for resolving relative paths
    - In `forge_services/src/tools/fs/fs_undo.rs` - Update path resolution to use the conversation reference
    - In `forge_main/src/editor.rs` - Modify the editor initialization to use the active conversation's `cwd`
    - In `forge_services/src/tools/fs/fs_find.rs` - Update search functionality to use the provided conversation reference
    - Priority: High
    - Complexity: Medium
    - Dependencies: Steps 1-2
8.  Update references to `env.pid` in the codebase
    - In `forge_main/src/info.rs` - Remove the PID from information display or replace with current process PID using `std::process::id()` directly
    - Priority: Medium
    - Complexity: Low
    - Dependencies: Step 1
9.  Update tests to reflect the changes in Environment and Conversation structures
    - Priority: Medium
    - Complexity: Medium
    - Dependencies: Steps 1-10
10. Update the tool trait/interface definition
    - Modify tool interfaces to accept a reference to the `Conversation`
    - Update the tool execution flow to pass the conversation reference
    - Ensure all tool implementations use the conversation's context correctly
    - Priority: High
    - Complexity: Medium
    - Dependencies: Steps 2-7

## Verification Criteria

- All compilation errors are resolved: `cargo +nightly fmt --all; cargo +nightly clippy --fix --allow-staged --allow-dirty --workspace`
- All tests pass: `cargo insta test --accept --unreferenced=delete`
- The `Environment` struct no longer contains `cwd` and `pid` fields
- The `Conversation` struct correctly stores and provides access to the `cwd`
- All file system operations work correctly with the conversation-specific working directory

## Potential Risks and Mitigations

- Risk 1: Many parts of the codebase rely on `Environment::cwd` and may be missed during refactoring
  Mitigation: Use comprehensive code search to identify all instances, validate with thorough testing
- Risk 2: Changes to the `API` trait interface may break clients
  Mitigation: Ensure all implementations are properly updated, consider backward compatibility measures if needed
- Risk 3: File system operations may not work correctly if `cwd` is not properly passed through
  Mitigation: Carefully update file system tool implementations to use the conversation's `cwd`
- Risk 4: Existing serialized conversation data may not have a `cwd` field
  Mitigation: Implement migration logic or default values when deserializing existing data

## Alternative Approaches

1. Keep `cwd` in Environment but make it readonly: Instead of removing it completely, make it immutable and initialize it only once. This would reduce change scope but wouldn't fully solve the conceptual issue.
2. Introduce a separate Context object: Create a new type to hold context-specific information like `cwd` that could be passed around as needed, without modifying the Conversation structure. This would provide more flexibility but increase complexity.
3. Use thread-local storage: Store the current working directory in thread-local storage and access it when needed. This would minimize API changes but introduce potential thread safety issues and make testing harder.
