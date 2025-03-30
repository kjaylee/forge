# Concise Implementation Plan: Event Names as Vectors and Configurable Modes

**Date**: 2025-03-22

## Objective

This plan addresses two key enhancements to the Code Forge project:

1. Replace string-based event names with vector-based representation
2. Make modes configurable in YAML instead of hardcoded enum values

## Implementation Summary

### Part 1: Vector-Based Event Names

1. **Update Event Structure**
   ```rust
   pub struct Event {
       pub id: String,
       pub name_parts: Vec<String>,  // Replace string 'name' with vector
       pub value: String,
       pub timestamp: String,
   }
   ```

2. **Core Methods**
   ```rust
   impl Event {
       // String conversion for compatibility
       pub fn name(&self) -> String {
           self.name_parts.join("/")
       }
       
       // Pattern matching for subscriptions
       pub fn matches_pattern(&self, pattern: &str) -> bool {
           let name_str = self.name();
           match regex::Regex::new(pattern) {
               Ok(re) => re.is_match(&name_str),
               Err(_) => name_str == pattern,
           }
       }
       
       // Part access
       pub fn name_part(&self, index: usize) -> Option<&str> {
           self.name_parts.get(index).map(|s| s.as_str())
       }
   }
   ```

3. **Update Areas**
   - Replace direct `event.name` accesses with `event.name()` method calls
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

1. **Event Name Changes**
   - Direct accesses: `conversation.rs`, `ui.rs`, `model.rs` 
   - Subscription matching: `conversation.rs`
   - Templates: All Handlebars templates using `event.name`

2. **Mode Changes**
   - Workflow structure: Add ModeConfig structure
   - State: Replace Mode enum with string-based representation
   - Command handling: Update to support dynamic modes
   - UI: Update mode switching and event creation

## Implementation Strategy

1. Create a dedicated branch for implementation
2. First implement vector-based event names
   - Update Event structure
   - Add compatibility methods
   - Fix affected code areas
3. Then implement configurable modes
   - Update Workflow structure
   - Replace Mode enum
   - Update command handling
4. Run all tests to verify both changes
5. Document the changes

## Verification Criteria

1. All existing code works with the new event name structure
2. Custom modes can be defined and used through configuration
3. Dynamic mode commands work as expected
4. Event name subscriptions continue to work accurately