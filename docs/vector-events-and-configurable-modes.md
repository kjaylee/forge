# Vector-Based Event Names & Configurable Modes Implementation

**Date**: 2025-03-22

This document describes the implementation of two key enhancements to the Code Forge project:

1. Replacing string-based event names with vector-based representation (breaking change)
2. Making modes configurable in YAML instead of hardcoded enum values

## Vector-Based Event Names

The event system has been updated to use a vector-based representation for event names instead of plain strings. This allows for more structured event handling and easier manipulation of event path components.

### Key Changes

1. **Event Structure**

   The `Event` struct now uses a vector for the name field:
   ```rust
   pub struct Event {
       pub id: String,
       pub name: Vec<String>,  // Changed from String to Vec<String>
       pub value: String,
       pub timestamp: String,
   }
   ```

2. **New Methods**

   - `name_string()` - Converts the vector to a string (joins with "/")
   - `matches_pattern()` - Checks if an event matches a pattern
   - `name_part()` - Gets a specific part of the event name path

3. **Updated Constructors**

   - `Event::new()` - Takes a vector directly
   - `Event::from_path()` - Compatibility method that takes a string path and splits it

4. **Compatibility**

   - Added `Display` trait implementation for easy string conversion
   - Added `PartialEq` implementation for string comparison

### Usage Examples

Creating events:
```rust
// Using vector directly
let event1 = Event::new(vec!["user".to_string(), "task_init".to_string()], "value");

// Using string path (backward compatible)
let event2 = Event::from_path("user/task_init", "value");
```

Accessing event name:
```rust
// Get full path as string
let name_str = event.name_string();  // "user/task_init"

// Get specific part
if let Some(first_part) = event.name_part(0) {
    println!("First part: {}", first_part);  // "user"
}
```

## Configurable Modes

The application now supports configurable modes through the YAML configuration file instead of using a hardcoded enum.

### Key Changes

1. **Mode Structure**

   Replaced enum with a string-based representation:
   ```rust
   pub struct Mode(String);
   ```

2. **YAML Configuration**

   Modes are defined in the YAML configuration file:
   ```yaml
   # Mode configuration
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
   ```

3. **Dynamic Command Handling**

   - The `ForgeCommandManager` has been updated to register mode commands dynamically
   - The parse method now handles dynamic mode commands with special handling

### Adding Custom Modes

To add a custom mode, simply add it to the `modes` section in the YAML configuration:

```yaml
modes:
  # ... existing modes ...
  - name: ANALYZE
    description: "Performs code analysis without making changes"
    command: "/analyze"
```

The mode will automatically be available as a command (e.g., `/analyze`) and will be used in event prefixes (e.g., `analyze/user/task_init`).

## Migration Notes

This is an intentional breaking change. All code that directly uses `event.name` assuming it's a string will need to be updated:

1. For string representation: Use `event.name_string()`
2. For direct vector operations: Use `event.name` as a vector
3. For event creation: Prefer `Event::new(vec![...])` or use `Event::from_path()`

## Implementation Details

The implementation follows the plan outlined in `plans/event-name-breaking-change-2025-03-22.md` with careful attention to maintaining backward compatibility where possible.