# Environment Refactor

## Objective

Refactor the `Environment` struct by removing `cwd` and `pid` fields, while ensuring all dependent parts of the codebase are updated to maintain functionality. Additionally, ensure we always use the CWD from Conversation only and not end up using std::env or other hacks, move the loader into ForgeServices, and update the Conversation service to use paths directly.

## Implementation Plan

## Detailed Implementation Notes

### Conversation Updates

1. Add `pub cwd: PathBuf` field to the `Conversation` struct
2. Update `Conversation::new()` constructor to take a `cwd: PathBuf` parameter and store it
3. Add a `path()` or `cwd()` helper method to easily access the working directory

### API Method Changes

1. Update the `init` method signature to: `async fn init(&self, path: PathBuf) -> anyhow::Result<ConversationId>`
2. The method will look for a workflow configuration in the provided path
3. If no workflow configuration exists, use the default workflow
4. Use the provided path as the conversation's working directory

### Tool Implementation Updates

1. Update the `ExecutableTool` trait to include a reference to the `Conversation` in its method signature
2. All tool implementations will be updated to use this new signature
3. The `call` method will change from `call(&self, input: Self::Input) -> anyhow::Result<String>` to `call(&self, input: Self::Input, conversation: &Conversation) -> anyhow::Result<String>`
4. File system tools will directly access the conversation's `cwd` field via this reference
5. Update the `JsonTool` adapter and `ForgeToolService` to properly pass the conversation reference
6. This approach ensures tools always have access to the correct working directory context
7. Create a backwards compatibility layer for old persisted data that lacks the `cwd` field

### Loader Relocation

1. Move the loader from `forge_api` to `forge_services`
2. Update all imports and references to the loader throughout the codebase
3. Ensure the loader can be used easily by the Conversation service for loading workflows

### Conversation Service Updates

1. Update the Conversation service's create method to take a path instead of a workflow
2. Use the relocated loader to load the workflow from the provided path
3. Ensure the path is properly set as the conversation's cwd

### Comprehensive CWD Usage Guidelines

To ensure consistent and correct CWD usage throughout the codebase, follow these guidelines:

1. **Never Use std::env For CWD**:
   1.1. Replace all instances of `std::env::current_dir()` with references to the conversation's CWD
   1.2. This includes code in utilities, tools, and helper functions
   1.3. The only allowed usage of `std::env::current_dir()` is at application entry points

2. **Entry Points**:
   2.1. Main CLI entry point should capture the initial CWD using `std::env::current_dir()`
   2.2. Pass this captured CWD to the conversation creation process
   2.3. Never re-query the current directory after initialization

3. **Pass-Through Pattern**:
   3.1. Functions that need access to CWD should receive it as a parameter
   3.2. Avoid storing CWD in global state or thread-local storage
   3.3. When creating new functions that need CWD, explicitly include a PathBuf parameter

4. **Tool Context**:
   4.1. Tools should always receive a reference to the Conversation
   4.2. Use `conversation.cwd` to access the current working directory
   4.3. Never derive paths using absolute locations other than the conversation's CWD

5. **Path Resolution**:
   5.1. Always resolve relative paths against the conversation's CWD
   5.2. Create a helper function for path resolution if needed
   5.3. Standardize on using `conversation.cwd.join(relative_path)` pattern

6. **Testing**:
   6.1. In tests, always provide an explicit CWD rather than relying on the test environment
   6.2. Create test fixtures that initialize a Conversation with a specific CWD

### Changes

- For the scope of this refactoring, we'll focus only on the core functionality

1.  Modify `Environment` struct definition in `forge_domain/src/env.rs`
    1.1. Remove `cwd` field
    1.2. Remove `pid` field
    1.3. Update any methods that directly reference these fields
    Priority: High
    Complexity: Low
    Dependencies: None
2.  Update `Conversation` struct in `forge_domain/src/conversation.rs`
    2.1. Add a new `cwd` field of type `PathBuf`
    2.2. Modify the constructor to accept and store a `cwd` parameter
    2.3. Consider adding helper methods to access the cwd if needed
    Priority: High
    Complexity: Low
    Dependencies: Step 1
3.  Move the loader from `forge_api/src/loader.rs` to `forge_services`
    3.1. Create appropriate module structure in ForgeServices for the loader
    3.2. Update all imports and references to use the new location
    Priority: High
    Complexity: Medium
    Dependencies: None
4.  Update the Conversation service in `forge_services/src/conversation.rs`
    4.1. Modify the create method to take a path instead of a workflow
    4.2. Use the relocated loader to load the workflow from the provided path
    4.3. Ensure the path is properly set as the conversation's cwd
    Priority: High
    Complexity: Medium
    Dependencies: Steps 2 and 3
5.  Update the API trait in `forge_api/src/api.rs`
    5.1. Modify the `init` method signature to accept only a `path` parameter: `async fn init(&self, path: PathBuf) -> anyhow::Result<ConversationId>`
    5.2. Remove the workflow parameter as it will be loaded from the path
    5.3. Update the method documentation to reflect the new behavior
    Priority: High
    Complexity: Medium
    Dependencies: Steps 1-4
6.  Implement updated `init` method in `forge_api/src/forge_api.rs`
    6.1. Modify implementation to load workflow from the provided path
    6.2. Reuse existing workflow loading logic internally
    6.3. Create a new conversation with the loaded workflow and the path
    Priority: High
    Complexity: Medium
    Dependencies: Step 5

7.  Remove the `update_cwd` method from the `API` trait and its implementations
    7.1. This is no longer needed as `cwd` will be conversation-specific
    Priority: Medium
    Complexity: Low
    Dependencies: Steps 1-6

8.  Remove the `load` method from the `API` trait and its implementations
    8.1. Incorporate this functionality into the updated `init` method
    Priority: Medium
    Complexity: Medium
    Dependencies: Steps 5-6
9.  Update all references to `env.cwd` in the codebase
    9.1. In `forge_services/src/template.rs` - Modify the template creation to use the conversation reference's `cwd` instead of env's cwd
    9.2. In `forge_services/src/tools/fs/fs_write.rs` - Update tool implementation to access the conversation's `cwd` directly via reference
    9.3. In `forge_services/src/tools/fs/fs_read.rs` - Modify to use the passed conversation reference for resolving relative paths
    9.4. In `forge_services/src/tools/fs/fs_undo.rs` - Update path resolution to use the conversation reference
    9.5. In `forge_main/src/editor.rs` - Modify the editor initialization to use the active conversation's `cwd`
    9.6. In `forge_services/src/tools/fs/fs_find.rs` - Update search functionality to use the provided conversation reference
    Priority: High
    Complexity: Medium
    Dependencies: Steps 1-2

10. Update all instances of `std::env::current_dir()` usage throughout the codebase
    10.1. In `forge_main/src/main.rs` - Capture CWD only at application startup
    10.2. In `forge_main/src/cli.rs` - Update to pass captured CWD to initialization functions
    10.3. In any utilities that use std::env directly - Modify to accept explicit path parameters
    10.4. In test code that relies on current directory - Update to use explicit test paths
    Priority: High
    Complexity: Medium
    Dependencies: Steps 1-2

11. Update references to `env.pid` in the codebase
    11.1. In `forge_main/src/info.rs` - Remove the PID from information display or replace with current process PID using `std::process::id()` directly
    Priority: Medium
    Complexity: Low
    Dependencies: Step 1
12. Update tests to reflect the changes in Environment and Conversation structures
    12.1. Update test fixtures to include CWD in Conversation instances
    12.2. Update mocks of Environment to remove cwd and pid fields
    12.3. Adjust test expectations for file path resolution
    Priority: Medium
    Complexity: Medium
    Dependencies: Steps 1-11

13. Update the `ExecutableTool` trait definition in `forge_domain/src/tool_definition.rs`
    13.1. Change the trait signature to: `async fn call(&self, input: Self::Input, conversation: &Conversation) -> anyhow::Result<String>`
    13.2. Update the `JsonTool` adapter in `forge_domain/src/tool.rs` to properly pass the conversation reference
    13.3. Update the tool execution flow to pass the conversation reference
    Priority: High
    Complexity: Medium
    Dependencies: Steps 2-10

14. Update the `ForgeToolService` in `forge_services/src/tool_service.rs`
    14.1. Modify the `call` method to pass the conversation to the tools
    14.2. Ensure proper error handling and timeouts are maintained
    Priority: High
    Complexity: Low
    Dependencies: Step 13

15. Update all tool implementations to use the new `ExecutableTool` trait signature
    15.1. Update `ShowUser`, `Shell`, `FSList`, `FSFileInfo`, `Fetch`, and all other tool implementations
    15.2. Ensure all tools use the conversation's context correctly for path operations
    15.3. Follow the pattern `let path = conversation.cwd.join(some_relative_path)` for path resolutions
    Priority: High
    Complexity: Medium
    Dependencies: Step 13
    
16. Update all test implementations to handle the Conversation parameter
    16.1. Create proper test fixtures that initialize a Conversation with a specific CWD
    16.2. Update mock implementations of the `ExecutableTool` trait
    Priority: Medium
    Complexity: High
    Dependencies: Steps 13-15

17. Fix any code that uses `Conversation::default()` or similar patterns
    17.1. Update to properly initialize a Conversation with all required fields, including `cwd`
    17.2. Use appropriate defaults when necessary
    Priority: Medium
    Complexity: Medium
    Dependencies: Steps 13-16

## Verification Criteria

- All compilation errors are resolved: `cargo +nightly fmt --all; cargo +nightly clippy --fix --allow-staged --allow-dirty --workspace`
- All tests pass: `cargo insta test --accept --unreferenced=delete`
- The `Environment` struct no longer contains `cwd` and `pid` fields
- The `Conversation` struct correctly stores and provides access to the `cwd`
- All file system operations work correctly with the conversation-specific working directory
- The loader is successfully moved to ForgeServices and is used by the Conversation service
- The Conversation service's create method takes a path instead of a workflow
- No instances of `std::env::current_dir()` remain except at application entry points
- Path resolution is consistently handled using the conversation's CWD throughout the codebase

## Potential Risks and Mitigations

- Risk 1: Many parts of the codebase rely on `Environment::cwd` and may be missed during refactoring
  Mitigation: Use comprehensive code search to identify all instances, validate with thorough testing
- Risk 2: Changes to the `API` trait interface may break clients
  Mitigation: Ensure all implementations are properly updated, consider backward compatibility measures if needed
- Risk 3: File system operations may not work correctly if `cwd` is not properly passed through
  Mitigation: Carefully update file system tool implementations to use the conversation's `cwd`
- Risk 4: Existing serialized conversation data may not have a `cwd` field
  Mitigation: Implement migration logic or default values when deserializing existing data
- Risk 5: Moving the loader to ForgeServices might impact existing functionality
  Mitigation: Ensure all imports and references are updated, with thorough testing of workflow loading
- Risk 6: Hidden references to `std::env::current_dir()` might be missed during refactoring
  Mitigation: Use grep/search tools to identify all instances across the codebase, including in tests
- Risk 7: Breaking backward compatibility with existing tool implementations
  Mitigation: Ensure all implementations are updated and thoroughly tested with the new ExecutableTool trait signature
- Risk 8: Test failures due to the conversation parameter
  Mitigation: Carefully update all test cases to provide a properly initialized conversation with valid CWD

## Alternative Approaches

1. Keep `cwd` in Environment but make it readonly: Instead of removing it completely, make it immutable and initialize it only once. This would reduce change scope but wouldn't fully solve the conceptual issue.
2. Introduce a separate Context object: Create a new type to hold context-specific information like `cwd` that could be passed around as needed, without modifying the Conversation structure. This would provide more flexibility but increase complexity.
3. Use thread-local storage: Store the current working directory in thread-local storage and access it when needed. This would minimize API changes but introduce potential thread safety issues and make testing harder.
4. Use an implicit context object: Instead of updating the ExecutableTool trait to include a conversation parameter, create a thread-local context that tools can access. This would minimize code changes but introduce thread safety concerns and make testing more difficult.
5. Implement a backward compatibility layer: Create adapter traits or wrappers to maintain backward compatibility with existing tool implementations. This would add complexity but allow for a more gradual transition.
6. Use a default implementation: Provide a default implementation for the conversation parameter that creates a new conversation if one is not provided. This would require less code changes but might mask issues when the conversation's context is needed.