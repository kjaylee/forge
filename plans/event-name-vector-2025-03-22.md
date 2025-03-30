# Event Name Vector Implementation Plan

**Date**: 2025-03-22

## Objective

Enhance the `Event` structure in the `forge_domain` crate to convert the current string-based `name` field to a vector of strings, allowing for better handling of hierarchical event names while maintaining backward compatibility with existing code.

## Current Implementation Analysis

The `Event` structure in `forge_domain/src/event.rs` currently has these key properties:

1. **Simple String-Based Name**:
   - Event names are stored as simple strings: `pub name: String`
   - Hierarchical names like `"act/user/task_init"` are represented as a single string

2. **Event Usage Patterns**:
   - Event names are used for subscription matching with regex
   - Event names are compared directly for equality in multiple places
   - Templates reference event names using dot notation: `event.name`
   - UI code formats hierarchical event names using format strings

3. **Event Matching**:
   - Events are matched against subscription patterns using regex
   - Some code directly compares event names with `==` operator
   - The `conversation.rs` module has a `subscribers()` method that matches events against regex patterns

## Implementation Plan

### 1. Update Event Structure

Modify the `Event` structure in `forge_domain/src/event.rs` to include a vector representation of the name while preserving the original string:

```rust
pub struct Event {
    pub id: String,
    // Original string representation (for backward compatibility)
    pub name: String,
    // New vector representation
    pub name_parts: Vec<String>,
    pub value: String,
    pub timestamp: String,
}
```

### 2. Implement Conversion Logic

Add helper methods to automatically convert between the string and vector representations:

```rust
impl Event {
    // Existing methods...
    
    // Convert a string path to name parts
    fn path_to_parts(name: &str) -> Vec<String> {
        name.split('/')
            .map(|s| s.to_string())
            .collect()
    }
    
    // Convert name parts to a string path
    fn parts_to_path(parts: &[String]) -> String {
        parts.join("/")
    }
}
```

### 3. Update Event Constructor

Modify the `Event::new()` method to automatically populate both representations:

```rust
pub fn new(name: impl ToString, value: impl ToString) -> Self {
    let id = uuid::Uuid::new_v4().to_string();
    let timestamp = chrono::Utc::now().to_rfc3339();
    let name_str = name.to_string();
    let name_parts = Self::path_to_parts(&name_str);

    Self {
        id,
        name: name_str,
        name_parts,
        value: value.to_string(),
        timestamp,
    }
}
```

### 4. Add Accessor Methods

Add accessor methods to work with the new vector representation:

```rust
impl Event {
    // Get individual name part by index
    pub fn name_part(&self, index: usize) -> Option<&str> {
        self.name_parts.get(index).map(|s| s.as_str())
    }
    
    // Get the prefix (like "act" or "plan")
    pub fn prefix(&self) -> Option<&str> {
        self.name_part(0)
    }
    
    // Get the source (like "user" or "system")
    pub fn source(&self) -> Option<&str> {
        self.name_part(1)
    }
    
    // Get the action (like "task_init" or "task_update")
    pub fn action(&self) -> Option<&str> {
        self.name_part(2)
    }
    
    // Check if the event name starts with a specific prefix
    pub fn starts_with(&self, prefix: &str) -> bool {
        self.name.starts_with(prefix)
    }
    
    // Check if the event matches a specific pattern (compatible with current regex approach)
    pub fn matches_pattern(&self, pattern: &str) -> bool {
        match regex::Regex::new(pattern) {
            Ok(re) => re.is_match(&self.name),
            Err(_) => self.name == pattern,
        }
    }
}
```

### 5. Implement Name Setter

Provide a setter method that updates both representations:

```rust
impl Event {
    // Set a new name, updating both string and vector representations
    pub fn set_name(&mut self, name: impl ToString) {
        self.name = name.to_string();
        self.name_parts = Self::path_to_parts(&self.name);
    }
}
```

### 6. Add Type Conversions

Ensure the `Event` struct is still compatible with existing code:

```rust
// Implement AsRef<str> for compatibility with code that expects a string
impl AsRef<str> for Event {
    fn as_ref(&self) -> &str {
        &self.name
    }
}

// Implement Deref for Event to allow using it like a string (somewhat controversial)
impl std::ops::Deref for Event {
    type Target = str;
    
    fn deref(&self) -> &Self::Target {
        &self.name
    }
}

// Alternatively, we can implement PartialEq<&str> for Event
impl PartialEq<&str> for Event {
    fn eq(&self, other: &&str) -> bool {
        &self.name == other
    }
}

// And PartialEq<String> for Event
impl PartialEq<String> for Event {
    fn eq(&self, other: &String) -> bool {
        &self.name == other
    }
}
```

### 7. Update Serialization/Deserialization

Ensure proper serialization/deserialization with serde for the new structure:

```rust
// Custom serde implementation to handle both formats
// When deserializing from JSON, automatically convert string to parts
// When serializing to JSON, include both representations
```

## Areas Requiring Modifications

The following areas of the codebase will require modifications or verification to ensure compatibility:

1. **Direct String Comparisons**:
   - `conversation.rs:103`:  `.find(|event| event.name == event_name)`
   - `ui.rs:342`: `if event.name == EVENT_TITLE {`
   - All other places where `event.name` is compared with a string

2. **Template References**:
   - `forge.default.yaml:65`: `<event>{{event.name}}</event>`
   - All Handlebars templates that use `event.name`

3. **Subscription Matching**:
   - `conversation.rs:130`: `let subscribed_agents = self.subscribers(&event.name);`
   - All code that uses the `subscribers()` method

4. **Event Creation**:
   - `ui.rs:109`: `Event::new(format!("{mode}/{author}/{name}"), content)`
   - All code that constructs events with formatted names

## Potential Issues and Solutions

1. **Direct String Comparisons**:
   - These should continue to work if we implement proper trait implementations (PartialEq)
   - No changes needed if we use the string-based `name` field for comparisons

2. **Template References**:
   - Handlebars templates may need updates if they access individual parts
   - Could add helper functions for templates to access parts

3. **Serialization Format**:
   - JSON representation might change, affecting external integrations
   - Consider adding custom serialization/deserialization to maintain the same format

4. **Performance Considerations**:
   - The vector representation adds memory overhead
   - String splitting has a small performance cost
   - Consider caching split results to avoid repeated operations

## Verification Criteria

After implementing these changes, we should verify:

1. **Backward Compatibility**:
   - All existing tests should pass without modification
   - Existing code that uses event names as strings should continue to work

2. **New Functionality**:
   - Code can access individual parts of hierarchical event names
   - New helper methods work correctly

3. **Performance Impact**:
   - Measure any performance impact on event creation and matching
   - Ensure the overhead is acceptable

4. **Documentation**:
   - Update documentation to reflect the new structure
   - Provide examples of how to use the new vector representation

## Migration Plan

1. Implement the changes in a branch
2. Run all existing tests to ensure nothing breaks
3. Update any code that might benefit from the new vector representation
4. Document the new API for future use
5. Consider whether to deprecate direct access to the `name` field in favor of accessor methods