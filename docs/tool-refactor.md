# Tool Refactor - Agent Execution Guide

## Prerequisites

Environment Requirements:
- Rust version: stable (2021 edition)
- Required crates: All listed in Cargo.toml
- Build tools: cargo, git

Build Verification:
```bash
cargo check --workspace  # Must pass before starting
cargo test --workspace   # All tests must pass
```

## Architecture Overview

Domain Layer (forge_domain):
- Create service traits for each existing tool
- ForgeDomain trait will be extended to include tool services
- New ForgeTools trait will organize all tool-related services
- Error handling standardized on anyhow::Result throughout

Service Layer (forge_app):
- Implement service traits for each tool
- Maintain backward compatibility with existing interfaces
- Async operations:
  - Use async_trait only for tools requiring async operations
  - Support both sync and async operations in ToolCallService

## Implementation Guide

### Phase 1: Define Traits

Directory Structure:
- Review the 'tools' directory in forge_domain
- Organize traits by tool category
- Each tool gets its own module

Implementation Requirements:
- Create all service traits before implementation
- Standardize on anyhow::Result for error handling
- Define clear interfaces maintaining backward compatibility
- Document trait requirements and usage

### Phase 2: Create Tools

Implementation Strategy:
- Create tools vector similar to forge_tools/lib
- Tool creation depends only on new traits
- Use ToolDefinition trait for tool metadata
- JsonSchema derivation from structs

### Phase 3-6: Implementation through Optimization
[Previous phases content remains unchanged]

## Execution Instructions

### Documentation Format
- Keep documentation concise (1-2 lines per item)
- Use XML-style tags for structured content
- Each commit must reference task number

### Progress Tracking
- Update task status in <status> tag
- Record blockers in <blockers> tag
- Document completion criteria in <done> tag

### Current Task

<next_task>
task_id: 1
description: Create base trait structure in forge_domain/src/tools with category directories and core traits.
validation:
  - Directory structure matches specification
  - All mod.rs files present and correct
  - Compilation succeeds
  - Tests pass
error_handling:
  - If directories exist, verify structure
  - If compilation fails, review and fix each error
  - If tests fail, document and address each failure
completion_criteria:
  - All directories created and verified
  - mod.rs files contain correct exports
  - cargo check passes
  - cargo test passes
</next_task>

<tasks>
1. Create tools directory structure
   status: pending
   steps:
     - Verify forge_domain/src/tools exists
     - Verify category dirs: fs, net, code, process
     - Create/update mod.rs files
   validation:
     - Directory structure correct
     - mod.rs files present
     - Compilation successful

2. Define base traits
   status: pending
   prerequisites: task_1_complete
   steps:
     - Create base Tool trait
     - Define ToolError using anyhow
     - Create category traits
   validation:
     - Traits compile
     - Documentation present
     - Error handling correct

3. Move existing tools
   status: pending
   prerequisites: task_2_complete
   steps:
     - Migrate tools one category at a time
     - Update implementations
     - Verify each migration
   validation:
     - No functionality loss
     - All tests pass
     - Clean compilation

4. Documentation and tests
   status: pending
   prerequisites: task_3_complete
   steps:
     - Add trait docs
     - Update tests
     - Verify coverage
   validation:
     - Documentation complete
     - Tests passing
     - Coverage acceptable
</tasks>

<status>
current_phase: 1
current_task: 1
completion_percentage: 0
last_successful_validation: none
active_blockers: 0
</status>

<blockers>
</blockers>

<done>
criteria:
  - All tasks marked complete
  - All validations passing
  - No active blockers
  - Full test coverage maintained
  - Documentation updated
  - Clean cargo check
  - All tests passing
</done>

### Error Recovery Procedures

1. Compilation Failures
   - Document error message
   - Identify failed module
   - Review recent changes
   - Attempt targeted fix
   - If unsuccessful, revert to last known good state

2. Test Failures
   - Document failing tests
   - Reproduce locally
   - Review test requirements
   - Fix implementation or update test
   - Verify no regression

3. Integration Issues
   - Identify integration point
   - Verify interface compliance
   - Review error logs
   - Apply fixes incrementally
   - Validate full integration

### Commit Message Format

```
[Task-N] Brief description

- Detailed change 1
- Detailed change 2

Validation:
- List of validations performed

Fixes: #issue (if applicable)
```

### Agent Instructions

1. Always start by verifying prerequisites
2. Check current status before starting new task
3. Follow error recovery procedures when issues arise
4. Update status after each significant step
5. Document learnings as they occur
6. Use specified commit message format
7. Validate against completion criteria
8. Report blockers immediately

### Validation Requirements

For each task:
1. Compilation must succeed
2. Tests must pass
3. Documentation must be present
4. Code style must follow Rust guidelines
5. No warnings in cargo check
6. All error handling paths verified
