# Event Name Vector Implementation Plan (Replacement Approach)

**Date**: 2025-03-22

## Objective

Replace the current string-based `name` field in the `Event` structure with a vector-based representation (`name`), allowing for better handling of hierarchical event names while providing conversion methods to maintain compatibility with existing code.

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

Modify the `Event` structure in `forge_domain/src/event.rs` to replace the string-based `name` with a vector:

```rust
#[derive(Debug, Deserialize, Serialize, Clone, Setters)]
pub struct Event {
    pub id: String,
    // Replace single string with vector of parts    
    pub name: Vec<String>,
    pub value: String,
    pub timestamp: String,
}
```

### 2. Implement String Conversion Methods

Add methods to convert between vector representation and string representation:

```rust
impl Event {
    // Convert name parts to string representation
    pub fn name_as_str(&self) -> String {
        self.name.join("/")
    }  
}
```

### 3. Update Event Constructor

Modify the `Event::new()` method to handle the new representation:

```rust
pub fn new(name: impl ToString, value: impl ToString) -> Self {
    let id = uuid::Uuid::new_v4().to_string();
    let timestamp = chrono::Utc::now().to_rfc3339();
    let name_str = name.to_string();
    let name = name_str.split('/')
            .map(|s| s.to_string())
            .collect();

    Self {
        id,
        name,
        value: value.to_string(),
        timestamp,
    }
}
```

### 4. Add Accessor Methods

Add accessor methods for working with name parts:

```rust
impl Event {
    // Get individual name part by index
    pub fn name_part(&self, index: usize) -> Option<&str> {
        self.name.get(index).map(|s| s.as_str())
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
        self.name().starts_with(prefix)
    }
    
    // Match against a regex pattern (for compatibility with subscribers method)
    pub fn matches_pattern(&self, pattern: &str) -> bool {
        let name_str = self.name();
        match regex::Regex::new(pattern) {
            Ok(re) => re.is_match(&name_str),
            Err(_) => name_str == pattern,
        }
    }
}
```


### 8. Update UI Formatting

Update how UI formats events:

```rust
// Before:
Event::new(format!("{mode}/{author}/{name}"), content)

// After:
Event::new(vec![mode.to_string(), author.to_string(), name.to_string()], content)

// Alternative constructor overload for backward compatibility:
impl Event {
    pub fn new_from_parts(parts: Vec<String>, value: impl ToString) -> Self {
        let id = uuid::Uuid::new_v4().to_string();
        let timestamp = chrono::Utc::now().to_rfc3339();
        
        Self {
            id,
            name: parts,
            value: value.to_string(),
            timestamp,
        }
    }
}
```

## Areas Requiring Modifications

The following areas of the codebase will require modifications:

1. **Direct String Comparisons**:
   - `conversation.rs:103`:  `.find(|event| event.name == event_name)`
     - Replace with: `.find(|event| event.name() == event_name)`
   
   - `ui.rs:342`: `if event.name == EVENT_TITLE {`
     - Replace with: `if event.name() == EVENT_TITLE {`
   
   - All other places where `event.name` is compared with a string

2. **Template References**:
   - `forge.default.yaml:65`: `<event>{{event.name}}</event>`
     - Create a Handlebars helper that calls `.name()` when `.name` is accessed
     - Or update templates to use `{{event_name event}}` custom helper
   
   - All Handlebars templates that use `event.name`

3. **Event Creation**:
   - `ui.rs:109`: `Event::new(format!("{mode}/{author}/{name}"), content)`
     - Replace with: `Event::new_from_parts(vec![mode.to_string(), author.to_string(), name.to_string()], content)`
   
   - All code that constructs events with formatted names

4. **Subscription Matching**:
   - `conversation.rs:130`: `let subscribed_agents = self.subscribers(&event.name);`
     - Replace with: `let subscribed_agents = self.subscribers(&event.name());`
   
   - Update `subscribers()` method to handle vector-based names

## Code Areas That Need Changes 

### 1. Places Directly Using `event.name`:

- `conversation.rs:103`: `.find(|event| event.name == event_name)`
- `conversation.rs:130`: `let subscribed_agents = self.subscribers(&event.name);`
- `conversation.rs:173`: `let name = event.name.as_str();`
- `orch.rs:188`: `event_name = %event.name,`
- `ui.rs:342`: `if event.name == EVENT_TITLE {`
- `model.rs:249`: `Command::Custom(event) => &event.name,`

### 2. EventMessage and From<EventMessage> for Event:

```rust
// Before:
#[derive(Debug, JsonSchema, Deserialize, Serialize, Clone)]
pub struct EventMessage {
    pub name: String,
    pub value: String,
}

impl From<EventMessage> for Event {
    fn from(value: EventMessage) -> Self {
        Self::new(value.name, value.value)
    }
}

// After:
#[derive(Debug, JsonSchema, Deserialize, Serialize, Clone)]
pub struct EventMessage {
    pub name: String,  // Keep as string for API compatibility
    pub value: String,
}

impl From<EventMessage> for Event {
    fn from(value: EventMessage) -> Self {
        Self::new(value.name, value.value)  // Constructor handles conversion
    }
}
```

### 3. Handlebars Templates:

For all templates that use `event.name`, we need to add a Handlebars helper that returns the string representation:

```rust
// Add a Handlebars helper
handlebars.register_helper("event_name", Box::new(|params: &[serde_json::Value]| {
    // Extract the Event from params and call .name()
    if let Some(event) = params.get(0) {
        // Logic to extract the name from the Event
        // Return as HandlebarsJsonValue
    } else {
        // Return error
    }
}));
```

## Potential Issues and Solutions

1. **String Conversion Overhead**:
   - Converting from vector to string will happen frequently
   - Consider caching the string representation to avoid repeated joins
   - Use interior mutability to lazily compute the string form

2. **Template Compatibility**:
   - Handlebars templates expect `.name` to be a string
   - Will need custom helpers or to update all templates

3. **API Compatibility**:
   - External integrations may expect `name` to be a string field
   - Maintain compatibility in serialized form

4. **Performance Considerations**:
   - Vector operations may have different performance characteristics
   - String joins might be expensive in tight loops

## Verification Criteria

After implementing these changes, we should verify:

1. **Backward Compatibility**:
   - All existing code that accesses event names continues to work
   - All tests pass with the new implementation

2. **New Functionality**:
   - Code can directly access individual parts of event names
   - Operations are cleaner when working with hierarchical names

3. **Performance Impact**:
   - Measure any performance impact with benchmarks
   - Ensure the overhead of conversions is acceptable

4. **Documentation**:
   - Update all documentation to reflect the new structure
   - Provide clear examples of working with name parts

## Migration Plan

1. Create a branch for implementation
2. Update the `Event` structure to use vector representation
3. Add necessary conversion methods and trait implementations
4. Identify and update all places using `event.name` directly
5. Update template helpers to handle the new structure
6. Ensure serialization/deserialization maintains compatibility
7. Write tests to verify all functionality
8. Run existing tests to ensure backward compatibility
9. Create a detailed documentation/migration guide for teams