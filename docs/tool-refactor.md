# Tool Refactor

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

## Tool Organization

Tool Call Service:

- Purpose: Creates executable tools from service implementations
- Responsibilities:
  - Manages tool lifecycle
  - Handles both sync and async operations
  - Integrates with ForgeTools trait
  - Provides unified interface for tool execution

## Phase 1: Define Traits

Directory Structure:

- Review the 'tools' directory in forge_domain
- Organize traits by tool category
- Each tool gets its own module

Implementation Requirements:

- Create all service traits before implementation
- Standardize on anyhow::Result for error handling
- Define clear interfaces maintaining backward compatibility
- Document trait requirements and usage

## Phase 2: Create Tools

Implementation Strategy:

- Create tools vector similar to forge_tools/lib
- Tool creation depends only on new traits
- Use ToolDefinition trait for tool metadata:
  - Define input/output types
  - Specify execution requirements
  - Document tool capabilities
- JsonSchema derivation:
  - Derive from input/output structs
  - Maintain compatibility with existing schema

Migration Approach:

- Develop new implementation alongside existing code
- Keep both implementations active during development
- Final switch:
  - Single point of change
  - Zero downtime transition
  - Fallback capability if needed

## Phase 3: Service Implementation

Implementation in forge_app:

- Implement service traits for each tool
- Integration with ForgeDomain
- Connection with ForgeTools trait
- Maintain clean separation of concerns

## Phase 4: Verification

Testing Requirements:

- Unit tests:
  - New tests for service traits
  - New tests for implementations
  - Coverage for both sync/async operations
- Integration tests:
  - Port existing tests to new architecture
  - Verify tool interactions
  - Test ForgeTools integration
- Migration tests:
  - Verify both implementations during transition
  - Ensure behavior parity

## Phase 5: Review

Architecture Verification:

- Verify clean architecture principles:
  - Clear separation of concerns
  - Dependency rules followed
  - Interface segregation
- Code organization:
  - Proper module structure
  - Clear documentation
  - Consistent patterns

## Phase 6: Optimize

Performance Considerations:

- Optimization deferred for initial implementation
- Future optimization targets:
  - Tool execution efficiency
  - Resource usage
  - Async operation performance

# Execution Instructions

- Keep the documentation 1-2 lines only.
- Add you learnings based on user feedback in the <learnings> tag.
- Create a task list in the <tasks> tag.
- Use <next_task> to mark the next tag.

<next_task>
Create base trait structure in forge_domain/src/tools with category directories and core traits.
</next_task>

<tasks>
1. Create tools directory structure
   - Create directory: forge_domain/src/tools
   - Add category dirs: fs, net, code, process
   - Add mod.rs files

2. Define base traits

   - Create base Tool trait
   - Define ToolError type
   - Set up category-specific base traits

3. Move existing tools

   - Migrate file system tools
   - Migrate network tools
   - Migrate code analysis tools
   - Migrate process tools

4. Documentation and tests
   - Add trait documentation
   - Migrate existing tests
   - Verify compilation
     </tasks>

<learnings>
- Maintaining parallel implementations reduces risk
- Category-based organization improves maintainability
- Early documentation helps track progress
</learnings>
