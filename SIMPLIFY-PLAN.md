# Permission System Simplification Plan

## Core Goals
- Remove unnecessary abstractions
- Simplify configuration
- Streamline service layer
- Make code more maintainable
- Focus on essential functionality

## Current Pain Points
1. Service Layer:
   - Too many abstraction layers (Service, Manager, StateManager)
   - Complex interaction patterns
   - Overly generic interfaces

2. Configuration:
   - Overly complex YAML structure
   - Too many configuration options
   - Complex loading/parsing logic

3. Storage:
   - Split between session and config storage
   - Complex persistence logic
   - Unnecessary caching layers

## Simplification Phases

### Phase 1: Core Permission Types
1. Replace with simpler types:
```rust
pub enum Permission {
    Read,
    Write,
    Execute,
    Deny,
}

pub enum Policy {
    Always,
    Once,
    Session,
}

// Single configuration structure
pub struct PermissionConfig {
    default_policy: Policy,
    permissions: HashMap<Permission, Policy>,
    deny_patterns: Vec<String>,
}
```

### Phase 2: Configuration Simplification
1. Single YAML format:
```yaml
default_policy: session  # always, once, or session
permissions:
  read: always
  write: session
  execute: once
deny_patterns:
  - "**/secrets/**"
```

2. Remove:
- Complex directory configs
- Tool-specific overrides
- Multiple configuration layers

### Phase 3: Service Layer Simplification
1. Single Service:
```rust
pub struct PermissionService {
    config: PermissionConfig,
    path_validator: PathValidator,
    session_state: HashMap<(PathBuf, Permission), bool>,
}

impl PermissionService {
    pub fn check_permission(&self, path: &Path, permission: Permission) -> bool;
    pub fn update_permission(&mut self, path: &Path, permission: Permission, allowed: bool);
    pub fn validate_path(&self, path: &Path) -> Result<PathBuf>;
}
```

2. Remove:
- State manager
- Multiple storage layers
- Complex interaction patterns
- Generic trait implementations

### Phase 4: CLI Simplification
1. Simple prompt interface:
```rust
pub struct CliPrompt {
    pub fn request_permission(path: &Path, permission: &Permission) -> bool;
    pub fn display_result(path: &Path, permission: &Permission, allowed: bool);
}
```

2. Remove:
- Complex formatting options
- Multiple display modes
- Custom result types

## Implementation Plan

### Step 1: Core Cleanup
1. Delete files:
```
forge_domain/src/permission/
  - error.rs         (simplified errors)
  - interaction.rs   (removed)
  - request.rs       (simplified)
  - state.rs         (merged into core)
  - storage.rs       (simplified)
  - types.rs         (merged into core)
```

2. Create simplified core:
```
forge_domain/src/permission/
  - core.rs          (new simplified types)
  - config.rs        (simple config only)
  - service.rs       (streamlined service)
```

### Step 2: Service Implementation
1. Single service implementation:
- Merge functionality from manager and state_manager
- Remove trait abstractions
- Simplify error handling
- Direct permission checks

2. Simplified storage:
- In-memory session state only
- Simple YAML config loading
- No complex caching

### Step 3: CLI Updates
1. Streamline interface:
- Simple yes/no prompts
- Basic status display
- Remove complex formatting

2. Remove:
- Result formatting
- Display options
- Complex state tracking

## Testing Strategy
1. Focus on core functionality:
- Permission checks
- Path validation
- Basic config loading

2. Remove tests for:
- Complex abstractions
- Multiple storage types
- Generic implementations

## Documentation
1. Create:
- Simple usage guide
- Basic configuration examples
- Clear API documentation

2. Remove:
- Complex configuration docs
- Migration guides
- Backward compatibility notes

## Success Criteria
1. Simpler codebase:
- Fewer files
- Clear responsibility
- Direct implementation

2. Essential functionality:
- Permission checking
- Basic configuration
- Path validation
- CLI interaction

3. Improved maintainability:
- Less abstraction
- Clear flow
- Simple testing

## Next Steps
1. Remove unnecessary abstractions
2. Implement simplified core
3. Update service layer
4. Streamline CLI
5. Update documentation

## Non-Goals
- Backward compatibility
- Complex configuration options
- Multiple storage backends
- Generic trait implementations
- Complex state management