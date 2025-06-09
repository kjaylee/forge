# Task List Tool Split Implementation

## Objective

Split the monolithic `TaskList` tool in `crates/forge_services/src/tools/task_list.rs` into individual tools for each operation type (Append, Prepend, Next, Done, List), and update the agent configurations in `forge.default.yaml` to include the new individual tools for both software-engineer and software-designer agents.

## Implementation Plan

1. **Create new task tools directory structure**
   - Dependencies: None
   - Notes: Establish module structure following the pattern used by fs tools. Create dedicated directory for task-related tools.
   - Files: `crates/forge_services/src/tools/task/mod.rs`
   - Status: Not Started

2. **Define new input types for each operation**
   - Dependencies: Task 1
   - Notes: Create dedicated input structs to replace the generic Operation pattern. Each tool will have a specific input type instead of relying on enum dispatch.
   - Files: `crates/forge_domain/src/tool_input.rs`
   - Status: Not Started

3. **Implement TaskAdd tool for Append operation**
   - Dependencies: Task 2
   - Notes: Create dedicated tool for appending tasks to end of list. Include proper error handling and input validation following project patterns.
   - Files: `crates/forge_services/src/tools/task/task_add.rs`
   - Status: Not Started

4. **Implement TaskPrepend tool for Prepend operation**
   - Dependencies: Task 2
   - Notes: Create dedicated tool for prepending tasks to beginning of list. Share common functionality with TaskAdd where possible.
   - Files: `crates/forge_services/src/tools/task/task_prepend.rs`
   - Status: Not Started

5. **Implement TaskNext tool for Next operation**
   - Dependencies: Task 2
   - Notes: Create dedicated tool for getting next pending task (pop_front operation). Handle empty list scenarios gracefully.
   - Files: `crates/forge_services/src/tools/task/task_next.rs`
   - Status: Not Started

6. **Implement TaskDone tool for Done operation**
   - Dependencies: Task 2
   - Notes: Create dedicated tool for marking tasks as completed. Include TaskId input validation and next task identification.
   - Files: `crates/forge_services/src/tools/task/task_done.rs`
   - Status: Not Started

7. **Implement TaskList tool for List operation**
   - Dependencies: Task 2
   - Notes: Create dedicated tool for listing all tasks in markdown format. Maintain consistent formatting with existing implementation.
   - Files: `crates/forge_services/src/tools/task/task_list.rs`
   - Status: Not Started

8. **Move stats calculation to task service and update TaskListResult**
   - Dependencies: Tasks 3-7
   - Notes: Move Stats struct and calculation logic to `crates/forge_services/src/task.rs`. Update TaskListResult to use the moved Stats type for consistency across all task tools.
   - Files: `crates/forge_services/src/task.rs`, `crates/forge_services/src/tools/task_list.rs`
   - Status: Not Started

9. **Update tool registry to include new tools**
   - Dependencies: Tasks 3-7
   - Notes: Replace single TaskList registration with individual tool registrations. Ensure proper Infrastructure parameter passing.
   - Files: `crates/forge_services/src/tools/registry.rs`
   - Status: Not Started

10. **Update tools module exports**
    - Dependencies: Tasks 3-7, 9
    - Notes: Update module structure to export new task tools. Remove old task_list module reference.
    - Files: `crates/forge_services/src/tools/mod.rs`, `crates/forge_services/src/tools/task/mod.rs`
    - Status: Not Started

11. **Migrate and split existing tests**
    - Dependencies: Tasks 3-7
    - Notes: Distribute existing test cases across new tool implementations. Maintain insta snapshot testing approach and three-step test structure.
    - Files: Individual test modules in each new tool file
    - Status: Not Started

12. **Update agent configurations in forge.default.yaml**
    - Dependencies: Tasks 9-10
    - Notes: Replace `forge_tool_task_list` with individual tool names for both software-engineer and software-designer agents. Maintain tool functionality for both agent types.
    - Files: `forge.default.yaml`
    - Status: Not Started

13. **Verify compilation and test execution**
    - Dependencies: All previous tasks
    - Notes: Run cargo check, clippy, and test suite to ensure all changes integrate properly. Use project verification commands.
    - Files: All modified files
    - Status: Not Started

14. **Remove old task_list.rs implementation**
    - Dependencies: Tasks 12-13
    - Notes: Clean up old monolithic implementation after successful migration and verification.
    - Files: `crates/forge_services/src/tools/task_list.rs`
    - Status: Not Started

## Verification Criteria

- All new task tools compile successfully and pass clippy checks
- All existing test functionality is preserved across the split tools
- Both software-engineer and software-designer agents can access all task operations
- Tool registry properly exports all individual task tools
- No breaking changes to existing task service interfaces
- Insta snapshots are updated and all tests pass with `cargo insta test --accept --unreferenced=delete`
- Code formatting passes with `cargo +nightly fmt --all`

## Potential Risks and Mitigations

1. **Breaking Changes to Agent Workflows**
   Mitigation: Carefully coordinate the forge.default.yaml updates with tool registry changes. Test agent functionality thoroughly before removing old implementation.

2. **Shared State Consistency Issues**
   Mitigation: Ensure all new tools use the same Infrastructure instance and TaskService interface. Leverage existing TaskService state management rather than implementing new coordination logic.

3. **Input Type Migration Complexity**
   Mitigation: Design new input types to be simple and focused. Maintain clear mapping from old Operation enum to new input structures for easier migration.

4. **Test Coverage Gaps During Migration**
   Mitigation: Split existing tests methodically, ensuring each operation's test cases are properly distributed to corresponding new tools. Use insta snapshots to catch behavioral changes.

5. **Tool Registration and Discovery Issues**
   Mitigation: Follow existing patterns from fs tools directory. Ensure proper module exports and registry updates are coordinated together.

## Alternative Approaches

1. **Gradual Migration Approach**: Maintain both old monolithic tool and new individual tools temporarily, allowing for smoother transition and rollback capability. However, this adds complexity and temporary code duplication.

2. **Enum-Based Tool Selection**: Keep single tool but change input to select operation via enum parameter rather than embedded operation type. This is less disruptive but doesn't achieve the goal of true tool separation.

3. **Facade Pattern Implementation**: Create individual tool interfaces that delegate to shared implementation backend. This provides tool separation without full code splitting but may not provide the desired modularity benefits.