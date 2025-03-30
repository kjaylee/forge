# Concise Implementation Plan: Breaking Change Approach

**Date**: 2025-03-22

## Objective

This plan addresses two key enhancements to the Code Forge project:

1. Replace string-based event names with vector-based representation using a breaking change approach
2. Make modes configurable in YAML instead of hardcoded enum values

## Implementation Summary

### Part 1: Vector-Based Event Names (Breaking Change)

1. **Breaking Change to Event Structure**
   ```rust
   pub struct Event {
       pub id: String,
       pub name: Vec<String>,  // Same field name, but now a vector
       pub value: String,
       pub timestamp: String,
   }
   ```

2. **Core Methods**
   ```rust
   impl Event {
       // String conversion for compatibility
       pub fn name_string(&self) -> String {
           self.name.join("/")
       }
       
       // Pattern matching for subscriptions
       pub fn matches_pattern(&self, pattern: &str) -> bool {
           let name_str = self.name_string();
           match regex::Regex::new(pattern) {
               Ok(re) => re.is_match(&name_str),
               Err(_) => name_str == pattern,
           }
       }
       
       // Part access
       pub fn name_part(&self, index: usize) -> Option<&str> {
           self.name.get(index).map(|s| s.as_str())
       }
   }
   ```

3. **Constructor Updates**
   ```rust
   impl Event {
       // New constructor that takes vector directly
       pub fn new(name: Vec<String>, value: impl ToString) -> Self {
           let id = uuid::Uuid::new_v4().to_string();
           let timestamp = chrono::Utc::now().to_rfc3339();
           
           Self {
               id,
               name,
               value: value.to_string(),
               timestamp,
           }
       }
       
       // Compatibility constructor that takes string path
       pub fn from_path(path: impl ToString, value: impl ToString) -> Self {
           let path_str = path.to_string();
           let name = path_str.split('/')
               .map(|s| s.to_string())
               .collect();
           
           Self::new(name, value)
       }
   }
   ```

4. **Update Areas**
   - Replace direct `event.name` string operations with vector operations
   - Update string comparison to use `name_string()` method
   - Update event creation to use vector representation
   - Add compatibility traits (Display, PartialEq)

### Part 2: Configurable Modes

1. **YAML Configuration**
   ```yaml
   # Mode definitions in forge.default.yaml
   modes:
     - name: ACT
       description: "Executes commands and makes file changes"
       command: "/act"
     - name: PLAN
       description: "Plans actions without making changes"
       command: "/plan"
     - name: HELP
       description: "Answers questions"
       command: "/help"
     # Custom modes can be added here
   
   variables:
     mode: "ACT"  # Default mode
   ```

2. **String-Based Mode**
   ```rust
   // Replace enum with string representation
   pub struct Mode(String);
   
   impl Mode {
       pub fn new(value: impl ToString) -> Self {
           Self(value.to_string().to_uppercase())
       }
       
       pub fn as_str(&self) -> &str {
           &self.0
       }
   }
   ```

3. **Command Handling**
   - Update ForgeCommandManager to register mode commands dynamically
   - Replace hardcoded command variants with dynamic mode handling
   - Update UI to handle mode changes based on config

## Affected Code Areas

1. **Event Name Changes (Breaking)**
   - Direct accesses: All code referencing `event.name` as a string must be updated
   - String operations: `.split()`, `.startsWith()`, etc. must be replaced with vector operations
   - Subscription matching: `conversation.rs`
   - Templates: All Handlebars templates using `event.name`

2. **Mode Changes**
   - Workflow structure: Add ModeConfig structure
   - State: Replace Mode enum with string-based representation
   - Command handling: Update to support dynamic modes
   - UI: Update mode switching and event creation

## Implementation Strategy

1. Create a dedicated branch for implementation
2. First implement vector-based event names (breaking change)
   - Update Event structure to use `name: Vec<String>`
   - Add compatibility methods for string conversion
   - Fix all affected code areas with vector operations
3. Then implement configurable modes
   - Update Workflow structure
   - Replace Mode enum
   - Update command handling
4. Run all tests to verify both changes
5. Document the changes

## Verification Criteria

1. All code is updated to work with the new vector-based event name
2. Custom modes can be defined and used through configuration
3. Dynamic mode commands work as expected
4. Event name subscriptions continue to work accurately

## Migration Notes

This is an intentional breaking change. All code that directly uses `event.name` assuming it's a string will need to be updated. The migration paths are:

1. For string representation: Use `event.name_string()`
2. For direct vector operations: Use `event.name` as a vector
3. For event creation: Prefer `Event::new(vec![...])` over string paths