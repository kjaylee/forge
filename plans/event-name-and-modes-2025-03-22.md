# Combined Implementation Plan: Event Names as Vectors and Configurable Modes

**Date**: 2025-03-22

## Objective

This plan addresses two related enhancements to the Code Forge project:

1. Replace the current string-based `name` field in the `Event` structure with a vector-based representation (`name_parts`), allowing for better handling of hierarchical event names.

2. Make modes configurable in `forge.default.yaml` instead of hardcoding them as an enum, enabling custom modes beyond the current Act/Plan/Help options.

## Part 1: Vector-Based Event Names

### Current Implementation Analysis

The `Event` structure in `forge_domain/src/event.rs` currently has these key properties:

1. **Simple String-Based Name**:
   - Event names are stored as simple strings: `pub name: String`
   - Hierarchical names like `"act/user/task_init"` are represented as a single string

2. **Event Usage Patterns**:
   - Event names are used for subscription matching with regex
   - Event names are compared directly for equality
   - Templates reference event names using dot notation: `event.name`
   - UI code formats hierarchical event names using format strings

### Vector-Based Event Names Implementation Plan

#### 1. Update Event Structure

Modify the `Event` structure in `forge_domain/src/event.rs` to replace the string-based `name` with a vector:

```rust
#[derive(Debug, Deserialize, Serialize, Clone, Setters)]
pub struct Event {
    pub id: String,
    // Replace single string with vector of parts
    #[serde(rename = "name")]
    pub name_parts: Vec<String>,
    pub value: String,
    pub timestamp: String,
}
```

#### 2. Implement Essential Conversion Methods

Add core methods to convert between vector representation and string representation:

```rust
impl Event {
    // Convert name parts to string representation
    pub fn name(&self) -> String {
        self.name_parts.join("/")
    }
    
    // Convert a string path to name parts (for constructor)
    fn path_to_parts(name: &str) -> Vec<String> {
        name.split('/')
            .map(|s| s.to_string())
            .collect()
    }
    
    // Match against a regex pattern (for compatibility with subscribers method)
    pub fn matches_pattern(&self, pattern: &str) -> bool {
        let name_str = self.name();
        match regex::Regex::new(pattern) {
            Ok(re) => re.is_match(&name_str),
            Err(_) => name_str == pattern,
        }
    }
    
    // Get individual name part by index
    pub fn name_part(&self, index: usize) -> Option<&str> {
        self.name_parts.get(index).map(|s| s.as_str())
    }
}
```

#### 3. Update Event Constructor

Modify the `Event::new()` method to handle the new representation:

```rust
pub fn new(name: impl ToString, value: impl ToString) -> Self {
    let id = uuid::Uuid::new_v4().to_string();
    let timestamp = chrono::Utc::now().to_rfc3339();
    let name_str = name.to_string();
    let name_parts = Self::path_to_parts(&name_str);

    Self {
        id,
        name_parts,
        value: value.to_string(),
        timestamp,
    }
}

// Overload for direct vector input
pub fn new_from_parts(parts: Vec<String>, value: impl ToString) -> Self {
    let id = uuid::Uuid::new_v4().to_string();
    let timestamp = chrono::Utc::now().to_rfc3339();
    
    Self {
        id,
        name_parts: parts,
        value: value.to_string(),
        timestamp,
    }
}
```

#### 4. Implement Essential Traits

```rust
// Implement Display
impl std::fmt::Display for Event {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}

// Implement PartialEq<&str> for Event
impl PartialEq<&str> for Event {
    fn eq(&self, other: &&str) -> bool {
        self.name() == *other
    }
}

// Implement PartialEq<String> for Event
impl PartialEq<String> for Event {
    fn eq(&self, other: &String) -> bool {
        self.name() == *other
    }
}
```

## Part 2: Configurable Modes

### Current Implementation Analysis

1. **Hardcoded Mode Enum**:
   - Modes are currently defined as an enum in `forge_main/src/state.rs`
   - Only three hardcoded modes: Act, Plan, Help
   - Switching between modes uses hardcoded `/act`, `/plan`, `/help` commands

2. **Mode Usage**:
   - Mode is stored in the UIState structure
   - Mode is set as a variable in the conversation
   - Mode affects the format of event names (`"{mode}/{author}/{name}"`)
   - Mode is displayed in the UI after switching

### Configurable Modes Implementation Plan

#### 1. Remove Mode Enum

Replace the Mode enum in `state.rs` with a string-based representation:

```rust
// Before:
#[derive(Clone, Default)]
pub enum Mode {
    Plan,
    Help,
    #[default]
    Act,
}

// After:
#[derive(Clone, Default)]
pub struct Mode(String);

impl Default for Mode {
    fn default() -> Self {
        Self("ACT".to_string()) // Default mode from config or hardcoded fallback
    }
}

impl std::fmt::Display for Mode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Mode {
    pub fn new(value: impl ToString) -> Self {
        Self(value.to_string().to_uppercase())
    }
    
    pub fn as_str(&self) -> &str {
        &self.0
    }
}
```

#### 2. Update `forge.default.yaml` to Include Mode Definitions

Add a new section to define available modes:

```yaml
# Mode definitions
modes:
  - name: ACT
    description: "Executes commands and makes file changes"
    command: "/act"
  - name: PLAN
    description: "Plans actions without making changes"
    command: "/plan"
  - name: HELP
    description: "Answers questions and provides assistance"
    command: "/help"
  # Custom modes can be added here
  - name: DEBUG
    description: "Debug mode for development"
    command: "/debug"
  - name: DEMO
    description: "Demonstration mode with limited capabilities"
    command: "/demo"

# Default mode - must be one of the defined modes
variables:
  mode: "ACT"
```

#### 3. Create Mode Configuration Structures

Add a new structure to represent mode configuration:

```rust
// In forge_domain/src/workflow.rs
#[derive(Default, Debug, Clone, Serialize, Deserialize, Merge, Setters)]
#[setters(strip_option, into)]
pub struct ModeConfig {
    #[merge(strategy = crate::merge::std::overwrite)]
    pub name: String,
    
    #[merge(strategy = crate::merge::std::overwrite)]
    pub description: String,
    
    #[merge(strategy = crate::merge::std::overwrite)]
    pub command: String,
}

// Update the workflow structure to include modes
#[derive(Default, Debug, Clone, Serialize, Deserialize, Merge, Setters)]
#[setters(strip_option)]
pub struct Workflow {
    // Existing fields...
    
    #[merge(strategy = crate::merge::vec::append)]
    #[serde(default)]
    pub modes: Vec<ModeConfig>,
    
    // Other fields...
}
```

#### 4. Update Command and Event Creation

Update the command handling in `model.rs` to be dynamic:

```rust
// Instead of hardcoded command variants:
pub enum Command {
    // Other commands...
    Act,
    Plan,
    Help,
    // etc.
}

// Create a more generic mode change command:
pub enum Command {
    // Other commands...
    ChangeMode(String), // Takes the mode name
    // etc.
}
```

#### 5. Update UI to Handle Dynamic Modes

Update the UI to handle dynamic mode changes:

```rust
// In ui.rs
async fn handle_mode_change(&mut self, mode_name: &str) -> Result<()> {
    // Find the mode config by name
    let mode = self.workflow.modes
        .iter()
        .find(|m| m.name.eq_ignore_ascii_case(mode_name))
        .ok_or_else(|| anyhow::anyhow!("Unknown mode: {}", mode_name))?;
    
    // Update state
    self.state.mode = Mode::new(&mode.name);
    
    // Set variable in conversation
    let conversation_id = self.init_conversation().await?;
    self.api
        .set_variable(
            &conversation_id,
            "mode".to_string(),
            Value::from(mode.name.as_str()),
        )
        .await?;
    
    // Display mode message
    CONSOLE.write(
        TitleFormat::success(&mode.name)
            .sub_title(&mode.description)
            .format(),
    )?;
    
    Ok(())
}
```

#### 6. Update ForgeCommandManager to Register Mode Commands

Update the command registration to include modes from config:

```rust
pub fn register_all(&self, workflow: &Workflow) {
    let mut guard = self.commands.lock().unwrap();
    let mut commands = Self::default_commands();
    
    // Add workflow commands
    commands.extend(workflow.commands.clone().into_iter().map(|cmd| {
        let name = format!("/{}", cmd.name);
        let description = format!("⚙ {}", cmd.description);
        let value = cmd.value.clone();
        
        ForgeCommand { name, description, value }
    }));
    
    // Add mode commands
    commands.extend(workflow.modes.clone().into_iter().map(|mode| {
        ForgeCommand {
            name: mode.command.clone(),
            description: format!("Switch to {} mode - {}", mode.name, mode.description),
            value: Some(mode.name.clone()),
        }
    }));
    
    commands.sort_by(|a, b| a.name.cmp(&b.name));
    
    *guard = commands;
}
```

#### 7. Update Command Parsing

Update the command parsing to handle dynamic mode commands:

```rust
pub fn parse(&self, input: &str) -> anyhow::Result<Command> {
    let trimmed = input.trim();
    let is_command = trimmed.starts_with("/");
    if !is_command {
        return Ok(Command::Message(trimmed.to_string()));
    }
    
    // Handle standard commands
    match trimmed {
        "/new" => Ok(Command::New),
        "/info" => Ok(Command::Info),
        "/exit" => Ok(Command::Exit),
        "/models" => Ok(Command::Models),
        "/dump" => Ok(Command::Dump),
        text => {
            // Parse as potential mode command or custom command
            let parts = text.split_ascii_whitespace().collect::<Vec<&str>>();
            
            if let Some(command_text) = parts.first() {
                if let Some(command) = self.find(command_text) {
                    // If this is a mode command (check by finding it in modes list)
                    if let Some(mode_config) = self.workflow.modes.iter()
                        .find(|m| m.command == command.name) {
                        return Ok(Command::ChangeMode(mode_config.name.clone()));
                    }
                    
                    // Otherwise handle as custom command
                    let value = self.extract_command_value(&command, &parts[1..]);
                    
                    Ok(Command::Custom(PartialEvent::new(
                        command.name.clone().strip_prefix('/').unwrap().to_string(),
                        value.unwrap_or_default(),
                    )))
                } else {
                    Err(anyhow::anyhow!("{} is not valid", command_text))
                }
            } else {
                Err(anyhow::anyhow!("Invalid Command Format."))
            }
        }
    }
}
```

## Code Areas Requiring Modifications

### Event Name Vector Changes:

1. **Direct String Comparisons**:
   - `conversation.rs:103`:  `.find(|event| event.name == event_name)`
   - `ui.rs:342`: `if event.name == EVENT_TITLE {`
   - `model.rs:249`: `Command::Custom(event) => &event.name,`

2. **Template References**:
   - `forge.default.yaml:65`: `<event>{{event.name}}</event>`
   - All Handlebars templates that use `event.name`

3. **EventMessage and From<EventMessage> for Event**:
   - Update to handle the new vector-based approach

### Configurable Modes Changes:

1. **State Module**:
   - Replace Mode enum with string-based representation
   - Update related code to use string modes

2. **Model Module**:
   - Replace hardcoded mode commands with dynamic mode handling
   - Update Command enum to support dynamic modes

3. **UI Module**:
   - Update the mode switching logic to handle any mode name
   - Update event naming to use the mode string

4. **Templates**:
   - Update any templates that use hardcoded mode names

## Verification Criteria

After implementing these changes, we should verify:

1. **Vector-Based Event Names**:
   - All existing code that accesses event names continues to work
   - All tests pass with the new implementation
   - Code can directly access individual parts of event names
   - `matches_pattern()` works correctly for regex matching

2. **Configurable Modes**:
   - All standard modes (ACT, PLAN, HELP) continue to work
   - Custom modes can be added in configuration
   - Mode commands work as expected (`/act`, `/plan`, `/help`, custom commands)
   - Mode-specific templates and behaviors work with all modes

3. **Combined Functionality**:
   - Event names properly include the configured mode
   - Mode changes affect event name generation
   - Subscription matching works with all modes

## Migration Plan

1. Create a branch for implementation
2. First implement the vector-based event names
   - Update Event structure and methods
   - Fix all affected code areas
   - Run tests to verify functionality
3. Then implement configurable modes
   - Update Workflow structure to include mode definitions
   - Replace Mode enum with string-based representation
   - Update command handling to support dynamic modes
   - Run tests to verify functionality
4. Document the changes for other developers
5. Submit PR for review