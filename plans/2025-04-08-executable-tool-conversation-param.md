# Update ExecutableTool Trait to Pass Conversation Reference

## Objective

Update the `ExecutableTool` trait to include a reference to the `Conversation` in its method signature, and update all implementations throughout the codebase to maintain functionality. This change supports the environment refactoring by ensuring all tools have direct access to the conversation's working directory.

## Implementation Plan

1. Update the `ExecutableTool` trait definition in `forge_domain/src/tool_definition.rs`
   Priority: High
   Complexity: Low
   Dependencies: None

2. Fix the `JsonTool` adapter in `forge_domain/src/tool.rs` to properly pass the conversation
   Priority: High
   Complexity: Medium
   Dependencies: Step 1

3. Fix the default implementation of `Conversation` in `JsonTool`
   Priority: High
   Complexity: Low
   Dependencies: Step 1

4. Update the `ForgeToolService` in `forge_services/src/tool_service.rs`
   Priority: High
   Complexity: Low
   Dependencies: Step 1

5. Update the `ShowUser` tool implementation in `forge_services/src/tools/show_user.rs`
   Priority: High
   Complexity: Low
   Dependencies: Step 1

6. Update the `Shell` tool implementation in `forge_services/src/tools/shell/shell_tool.rs`
   Priority: High
   Complexity: Medium
   Dependencies: Step 1

7. Update the `FSList` tool implementation in `forge_services/src/tools/fs/fs_list.rs`
   Priority: High
   Complexity: Medium
   Dependencies: Step 1

8. Update the `FSFileInfo` tool implementation in `forge_services/src/tools/fs/file_info.rs`
   Priority: High
   Complexity: Medium
   Dependencies: Step 1

9. Update the `Fetch` tool implementation in `forge_services/src/tools/fetch.rs`
   Priority: High
   Complexity: Medium
   Dependencies: Step 1

10. Update all other tool implementations throughout the codebase
    Priority: High
    Complexity: Medium
    Dependencies: Step 1

11. Update all test implementations to handle the conversation parameter
    Priority: Medium
    Complexity: High
    Dependencies: Steps 1-10

12. Fix any regressions or compilation errors that arise
    Priority: High
    Complexity: Medium
    Dependencies: Steps 1-11

## Detailed Implementation Notes

### 1. Update ExecutableTool Trait

The `ExecutableTool` trait in `forge_domain/src/tool_definition.rs` needs to be updated to include a reference to the `Conversation`:

```rust
#[async_trait::async_trait]
pub trait ExecutableTool {
    type Input: DeserializeOwned;

    async fn call(&self, input: Self::Input, conversation: &Conversation) -> anyhow::Result<String>;
}
```

### 2. Update JsonTool Adapter

The `JsonTool` adapter in `forge_domain/src/tool.rs` needs to be updated to properly pass the conversation reference:

```rust
#[async_trait::async_trait]
impl<T: ExecutableTool + Sync> ExecutableTool for JsonTool<T>
where
    T::Input: serde::de::DeserializeOwned + JsonSchema,
{
    type Input = Value;

    async fn call(&self, input: Self::Input, conversation: &Conversation) -> anyhow::Result<String> {
        let input: T::Input = serde_json::from_value(input)?;
        self.0.call(input, conversation).await
    }
}
```

### 3. Fix Test Implementations

For tests that use mock implementations of the `ExecutableTool` trait, we need to ensure they handle the conversation parameter correctly:

```rust
struct MockTool;

#[async_trait::async_trait]
impl ExecutableTool for MockTool {
    type Input = SomeInputType;

    async fn call(&self, input: Self::Input, conversation: &Conversation) -> anyhow::Result<String> {
        // Implementation for test
        Ok("Mock response".to_string())
    }
}
```

### 4. Conversation Default Implementation

Make sure any places that currently use `Conversation::default()` are updated to handle creating a Conversation with the required fields including `cwd`:

```rust
let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("/"));
let conversation = Conversation::new(
    ConversationId::generate(),
    Workflow::default(),
    cwd,
);
```

### 5. Tool Usage Guidelines

When updating tool implementations, follow these guidelines:

1. **Access the CWD**: Use `conversation.cwd` to access the current working directory
2. **Path Resolution**: Always resolve relative paths against the conversation's CWD
3. **Testing**: In tests, provide an explicit CWD rather than relying on the test environment

### 6. Common Update Pattern for Tools

Most tools will follow this pattern when updated:

```rust
#[async_trait::async_trait]
impl<F: Infrastructure> ExecutableTool for SomeTool<F> {
    type Input = SomeToolInput;

    async fn call(&self, input: Self::Input, conversation: &Conversation) -> anyhow::Result<String> {
        // Use conversation.cwd when needed for path operations
        let path = conversation.cwd.join(some_relative_path);
        
        // Rest of the implementation
        // ...
    }
}
```

### 7. ForgeToolService Update

The `ForgeToolService` in `forge_services/src/tool_service.rs` needs to be updated to pass the conversation to tools:

```rust
#[async_trait::async_trait]
impl ToolService for ForgeToolService {
    async fn call(&self, call: ToolCallFull, conversation: &Conversation) -> ToolResult {
        // ... existing code ...
        match self.tools.get(&name) {
            Some(tool) => {
                match timeout(TOOL_CALL_TIMEOUT, tool.executable.call(input, conversation)).await {
                    // ... existing code ...
                }
            }
            None => // ... existing code ...
        }
    }
}
```

## Verification Criteria

- All compilation errors are resolved: `cargo +nightly fmt --all; cargo +nightly clippy --fix --allow-staged --allow-dirty --workspace`
- All tests pass: `cargo insta test --accept --unreferenced=delete`
- The `ExecutableTool` trait is consistently implemented across all tools
- All tools correctly use the conversation reference for path operations
- No regressions in functionality, especially for file system operations
- No places remaining where `std::env::current_dir()` is used for CWD access within tools

## Potential Risks and Mitigations

- Risk 1: Missing some tool implementations during the update
  Mitigation: Use comprehensive code search to identify all implementations, verify with compilation

- Risk 2: Breaking backward compatibility with existing tool implementations
  Mitigation: Ensure all implementations are updated and tested thoroughly

- Risk 3: Path resolution issues with the conversation's CWD
  Mitigation: Verify all path operations in tools work correctly with the updated approach

- Risk 4: Test failures due to the conversation parameter
  Mitigation: Carefully update all test cases to provide a properly initialized conversation

- Risk 5: Hidden references to `Environment` struct or `std::env::current_dir()` might be missed
  Mitigation: Use search tools to identify all instances across the codebase, including in tests

## Alternative Approaches

1. **Use an implicit context object**: Instead of updating the trait to include a conversation parameter, create a thread-local context that tools can access. This would minimize code changes but introduce thread safety concerns and make testing more difficult.

2. **Implement a backward compatibility layer**: Create adapter traits or wrappers to maintain backward compatibility with existing tool implementations. This would add complexity but allow for a more gradual transition.

3. **Use a default implementation**: Provide a default implementation for the conversation parameter that creates a new conversation if one is not provided. This would require less code changes but might mask issues when the conversation's context is needed.