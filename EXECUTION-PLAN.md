<user_feedback>
<!-- Phase 1.1 Permission States -->
- Need to handle permission states clearly in error messages
- Consider adding descriptions for error cases
- Think about permission hierarchy (does Forever override Session?)

<!-- Phase 1.2 Permission Request -->
- Consider adding validation for path existence
- May need custom Display implementation for better error messages
- Consider adding request merging for batch operations
- Handle path normalization for cross-platform compatibility
- Add more comprehensive error handling for edge cases
</user_feedback>

<agent_learnings>
<!-- Phase 1.1 Permission States Implementation -->
- Added comprehensive unit tests including serialization
- Helper methods improve code clarity and maintainability
- Clear separation between config and session storage logic
- Added documentation for public API

<!-- Phase 1.2 Permission Request Implementation -->
- Builder pattern with context provides flexibility
- String conversion helps with user interaction/logging
- Immutable getters prevent unexpected state changes
- Clone implementation enables request reuse

<!-- Phase 1.2.1 Implementation Learnings -->
- Don't modify existing tests without discussion
- Default trait isn't needed for unit-like structs
- Test infrastructure code should be in test modules
- Generic assertions should preserve test intent
- Consider interaction between domain and tool layers carefully

<!-- Phase 1.3 Storage Trait Implementation -->
- Keep trait definitions focused and minimal
- Use specific error types for better error handling
- Provide clear documentation for trait methods
- Consider async implications in trait design

<!-- Phase 2.1 Session Storage Implementation -->
- Arc<RwLock<T>> provides efficient thread-safe storage
- String keys better than PathBuf for hash maps
- Clear() method important for session cleanup
- Comprehensive tests needed for concurrent scenarios

<!-- Phase 2.2 Config Storage Implementation -->
- File locking essential for concurrent access safety
- YAML format provides human-readable storage
- Version field enables future format migrations
- Test both file creation and modification flows

<!-- Phase 3.1 CLI Communication Implementation -->
- Timeout handling requires careful error propagation
- Case-insensitive input improves user experience
- Context-aware formatting helps decision making
- Mock testing enables reliable timeout verification

<!-- Phase 3.3 Integration Tests Implementation -->
- Implemented mock input system for testing interactions.
- Added tests for timeout handling to ensure robustness.
- Tested error conditions to validate error handling logic.
- Tested message formatting to ensure correct output.
</agent_learnings>

# Permission System Enhancement: Execution Plan

## Project Understanding

### Core Architecture
1. **Domain Layer** (`forge_domain`)
   - Core domain models
   - Interface definitions
   - Error handling

2. **Tool Layer** (`forge_tool`)
   - Tool implementations 
   - Permission services
   - User interaction

3. **Server Layer** (`forge_server`)
   - API endpoints
   - Configuration management
   - Database interactions

### Key Components
1. **Permission System**
   - `PermissionService` trait
   - YAML configuration
   - File system validation
   - Tool-specific permissions

2. **Tool Framework**
   - Tool definitions
   - Execution pipeline
   - Error propagation
   - Usage prompts

## Enhancement Goals

1. **Default Interactive Mode**
   - User prompts for undefined permissions
   - Multiple persistence levels
   - Clear user interface
   - Session-based storage

2. **Storage Hierarchy**
   - Config file (permanent)
   - Session memory (temporary)
   - One-time decisions
   - Directory-based permissions

## Detailed Todo List

### Phase 1: Core Domain Updates
- [x] **1.1 Permission States** (1 day)
  ```rust
  // forge_domain/src/permission/state.rs
  pub enum PermissionState {
      Reject,
      Allow,
      AllowSession,
      AllowForever,
  }
  ```
  - [x] Add serialization derives
  - [x] Implement helper methods
  - [x] Add unit tests
  - [x] Update existing usages

- [x] **1.2 Permission Request** (1 day)
  ```rust
  // forge_domain/src/permission/request.rs
  pub struct PermissionRequest {
      path: PathBuf,
      tool_name: String,
      operation: String,
      context: Option<String>,
  }
  ```
  - [x] Add builder methods
  - [x] Implement validation
  - [x] Add conversion traits
  - [x] Write tests

- [x] **1.3 Storage Traits** (1 day)
  ```rust
  // forge_domain/src/permission/storage.rs
  pub trait PermissionStorage: Send + Sync {
      async fn load(&self, path: &Path, tool: &str) -> PermissionResult<Option<Permission>>;
      async fn save(&self, permission: Permission) -> PermissionResult<()>;
  }
  ```
  - [x] Define error types
  - [x] Add mock implementation
  - [x] Write storage tests
  - [x] Document trait methods

### Phase 2: Storage Implementation
- [x] **2.1 Session Storage** (2 days)
  ```rust
  // forge_tool/src/permission/storage/session.rs
  pub struct SessionStorage {
      permissions: Arc<RwLock<HashMap<(String, String), Permission>>>,
  }
  ```
  - [x] Implement thread-safe storage
  - [x] Add cleanup methods (clear(), len(), is_empty())
  - [x] Handle concurrent access with RwLock
  - [x] Write integration tests

- [x] **2.2 Config Storage** (2 days)
  ```rust
  // forge_tool/src/permission/storage/config.rs
  pub struct ConfigStorage {
      config_path: PathBuf,
  }
  ```
  - [x] YAML serialization with versioning support
  - [x] File locking with fs2 crate
  - [x] Handle non-existent paths
  - [x] Comprehensive error handling

- [x] **2.3 Storage Tests** (1 day)
  - [x] Unit tests for both storages
  - [x] Integration tests
  - [x] Performance tests
  - [x] Concurrent access tests

### Phase 3: User Interaction

- [x] **3.1 CLI Communication Flow** (1 day)
  ```rust
  // forge_domain/src/permission/interaction.rs
  #[async_trait]
  pub trait PermissionInteraction: Send + Sync {
      /// Request permission from user
      async fn request_permission(
          &self,
          request: &PermissionRequest
      ) -> PermissionResult<PermissionState>;

      /// Request permission with timeout
      async fn request_permission_timeout(
          &self,
          request: &PermissionRequest,
          timeout: Duration,
      ) -> PermissionResult<PermissionState>;

      /// Format permission request for display
      fn format_request(&self, request: &PermissionRequest) -> String;
  }

  // forge_tool/src/permission/cli.rs
  pub struct CliPermissionHandler {
      timeout: Duration,
  }

  impl CliPermissionHandler {
      pub fn parse_response(input: &str) -> PermissionResult<PermissionState> {
          match input.trim().to_uppercase().as_str() {
              "R" => Ok(PermissionState::Reject),
              "A" => Ok(PermissionState::Allow),
              "S" => Ok(PermissionState::AllowSession),
              "F" => Ok(PermissionState::AllowForever),
              _ => Err(PermissionError::InvalidResponse),
          }
      }
  }

  #[async_trait]
  impl PermissionInteraction for CliPermissionHandler {
      async fn request_permission(
          &self,
          request: &PermissionRequest
      ) -> PermissionResult<PermissionState> {
          self.request_permission_timeout(request, self.timeout).await
      }
  }
  ```
  - [x] Implement PermissionInteraction trait with timeout
  - [x] Create CLI handler with formatting
  - [x] Add timeout handling with tokio
  - [x] Case-insensitive input validation
  - [x] Human-friendly messages with context
  - [x] Comprehensive test suite

- [x] **3.2 LLM Integration** (1 day)
  ```rust
  // forge_tool/src/permission/result.rs
  #[derive(Debug, Clone)]
  pub struct PermissionResultDisplay {
      state: PermissionState,
      request: PermissionRequest,
      context: Option<String>,
  }
  ```
  - [x] Implement context-rich result formatting
  - [x] Add dual format modes (human/LLM)
  - [x] XML-like LLM output format
  - [x] Comprehensive test suite with snapshots

- [x] **3.3 Integration Tests** (1 day)
  ```rust
  #[tokio::test]
  async fn test_cli_interaction() {
      let handler = CliPermissionHandler::new();
      
      // Test request
      let request = PermissionRequest::new(
          "/test/path",
          "test_tool",
          "read"
      );

      // Mock user input
      let mock_input = MockInput::new()
          .with_response("A")
          .build();

      // Test interaction
      let result = handler
          .with_input(mock_input)
          .request_permission(&request)
          .await?;

      assert_eq!(result.state, PermissionState::Allow);
  }
  ```
  - [x] Implement mock input system
  - [x] Add timeout tests
  - [x] Test error conditions
  - [x] Test message formatting

### Phase 4: Permission Manager
- [x] **4.1 Core Manager** (2 days)
  ```rust
  // forge_tool/src/permission/manager.rs
  pub struct PermissionManager {
      session: SessionStorage,
      config: ConfigStorage,
  }
  ```
  - [x] Implement check flow
  - [x] Add caching
  - [ ] Handle errors
  - [x] Write tests

- [x] **4.2 Request Handler** (1 day)
  ```rust
  impl PermissionManager {
      pub async fn handle_request(&self, request: &PermissionRequest) -> PermissionResult<bool>
  }
  ```
  - [x] Implement decision flow
  - [ ] Add logging
  - [ ] Error handling
  - [x] Integration tests

### Phase 5: Tool Integration
- [ ] **5.1 Permission Service Updates** (2 days)
  ```rust
  // forge_domain/src/permission/service.rs
  impl PermissionService {
      pub async fn check_permission(&self, request: &PermissionRequest) -> PermissionResult<bool>
  }
  ```
  - [ ] Update trait methods
  - [ ] Add migration logic
  - [ ] Update documentation
  - [ ] Write tests

- [ ] **5.2 Tool Service Integration** (1 day)
  ```rust
  // forge_tool/src/tool_service.rs
  impl ToolService {
      async fn execute_with_permission(&self, tool: &Tool, args: &Value) -> Result<Value>
  }
  ```
  - [ ] Add permission checks
  - [ ] Update error handling
  - [ ] Write integration tests
  - [ ] Update docs

### Phase 6: Testing & Documentation
- [ ] **6.1 Test Suite** (2 days)
  - [ ] Unit tests for all components
  - [ ] Integration tests
  - [ ] Performance benchmarks
  - [ ] Edge case testing

- [ ] **6.2 Documentation** (1 day)
  - [ ] Update README
  - [ ] API documentation
  - [ ] Example usage
  - [ ] Migration guide

## Timeline
- **Phase 1**: 3 days
- **Phase 2**: 5 days
- **Phase 3**: 2 days
- **Phase 4**: 3 days
- **Phase 5**: 3 days
- **Phase 6**: 3 days

Total: 19 working days

## Dependencies
1. **Required Crates**
   - tokio (async runtime)
   - serde (serialization)
   - thiserror (error handling)
   - async-trait
   - parking_lot (RwLock)

2. **Internal Dependencies**
   - forge_domain
   - forge_tool
   - forge_walker

## Testing Strategy

### Unit Tests
1. **State Tests**
   ```rust
   #[test]
   fn test_permission_states() {
       // Test all state transitions
   }
   ```

2. **Storage Tests**
   ```rust
   #[tokio::test]
   async fn test_storage_operations() {
       // Test storage operations
   }
   ```

3. **Manager Tests**
   ```rust
   #[tokio::test]
   async fn test_permission_flow() {
       // Test complete flow
   }
   ```

### Integration Tests
1. **Tool Integration**
   ```rust
   #[tokio::test]
   async fn test_tool_with_permissions() {
       // Test tool execution with permissions
   }
   ```

2. **Config Integration**
   ```rust
   #[tokio::test]
   async fn test_config_persistence() {
       // Test config storage
   }
   ```

## Release Checklist
- [ ] All tests passing
- [ ] Documentation updated
- [ ] Examples added
- [ ] Migration guide written
- [ ] Performance benchmarks run
- [ ] Security review completed

## Post-Release Tasks
1. Monitor for:
   - Performance issues
   - Error patterns
   - User feedback

2. Plan follow-up improvements:
   - UI enhancements
   - Performance optimizations
   - Additional features
