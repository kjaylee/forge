# Task Service Extraction

## Objective
Extract task-related business logic from the TaskList tool into a dedicated TaskService, following the established service patterns in the codebase. The tool should become a simple wrapper that delegates all task operations to the service, maintaining clean separation of concerns between the tool layer and business logic.

## Implementation Plan

1. **Create TaskService Trait in App Layer**
   - Dependencies: None
   - Notes: Define comprehensive interface following existing service patterns like ConversationService and TemplateService
   - Files: `crates/forge_app/src/services.rs`
   - Status: Not Started

2. **Implement ForgeTaskService in Services Layer**
   - Dependencies: Task 1
   - Notes: Implement the service with thread-safe state management using Arc<Mutex<Vec<Task>>>, integrate with Infrastructure trait for file operations
   - Files: `crates/forge_services/src/task.rs`
   - Status: Not Started

3. **Update Services Trait to Include TaskService**
   - Dependencies: Task 1, Task 2
   - Notes: Add TaskService to the main Services trait and update ForgeServices implementation
   - Files: `crates/forge_app/src/services.rs`, `crates/forge_services/src/forge_services.rs`
   - Status: Not Started

4. **Refactor TaskList Tool to Use Service**
   - Dependencies: Task 1, Task 2, Task 3
   - Notes: Simplify tool to be a thin wrapper, delegate all business logic to service, maintain tool responsibilities like context updates and formatting
   - Files: `crates/forge_services/src/tools/task_list.rs`
   - Status: Not Started

5. **Update Infrastructure Integration**
   - Dependencies: Task 2
   - Notes: Ensure service has proper access to FsWriteService and EnvironmentService for markdown file generation
   - Files: `crates/forge_services/src/infra.rs` (if needed)
   - Status: Not Started

6. **Create Service Tests**
   - Dependencies: Task 2
   - Notes: Write comprehensive tests for the service layer using MockInfrastructure, test all operations and edge cases
   - Files: `crates/forge_services/src/task.rs`
   - Status: Not Started

7. **Update Tool Tests**
   - Dependencies: Task 4
   - Notes: Adapt existing tool tests to work with the new service-based implementation, ensure snapshot tests still pass
   - Files: `crates/forge_services/src/tools/task_list.rs`
   - Status: Not Started

8. **Compilation and Integration Testing**
   - Dependencies: All previous tasks
   - Notes: Run cargo commands to ensure compilation and test success, verify tool functionality end-to-end
   - Files: All modified files
   - Status: Not Started

## Verification Criteria
- All existing tests pass with the new service-based implementation
- TaskList tool becomes a thin wrapper with minimal business logic
- TaskService follows established patterns in the codebase (similar to ConversationService)
- Service is properly integrated with the Infrastructure trait
- Thread safety is maintained for concurrent task operations
- Markdown file generation continues to work as expected
- Code compilation succeeds without warnings

## Potential Risks and Mitigations

1. **State Management Complexity**
   Mitigation: Use the same Arc<Mutex<Vec<Task>>> pattern as the current implementation, ensure proper async/await handling

2. **Service Interface Design Mismatch**
   Mitigation: Start with high-level operations matching current tool operations, can be extended later with granular methods if needed

3. **Infrastructure Dependencies Breaking**
   Mitigation: Carefully analyze current infrastructure usage and ensure service has proper access to required services

4. **Test Refactoring Complexity**
   Mitigation: Keep service tests separate from tool tests, use existing MockInfrastructure patterns

5. **Tool Simplification Over-Engineering**
   Mitigation: Maintain essential tool responsibilities like ToolCallContext updates and result formatting

## Alternative Approaches

1. **Granular Service Interface**: Expose low-level methods (add_task, update_status, find_task) instead of high-level operations (append, prepend, mark_done)
2. **Persistent State**: Store tasks in a file or database instead of in-memory state
3. **Multiple Task Lists**: Support per-conversation or per-session task lists instead of a single global list
4. **Event-Driven Architecture**: Use events for task state changes to enable better extensibility and monitoring