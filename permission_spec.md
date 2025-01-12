# Permission System Refactor Specification

## Agent Guidelines
- Always read onboarding.md and service.md before starting
- Add agent_learning XML tags after each completed todo
- Ask for review after each significant change
- Update learnings based on user feedback

## Progress Tracking Format
```xml
<agent_learning>
  <!-- Knowledge and insights gained during implementation -->
  <concepts>
    - Understanding of X
    - Implementation of Y
  </concepts>
  <challenges>
    - Problem faced
    - How it was solved
  </challenges>
</agent_learning>

<user_feedback>
  <!-- Feedback received from reviews -->
  <feedback_item date="YYYY-MM-DD">
    - What was good
    - What needed improvement
  </feedback_item>
</user_feedback>
```

## Implementation Todos

### 1. Core Permission Types
Files to Delete:
- [ ] crates/forge_domain/src/permission/error.rs (old error types)
- [ ] crates/forge_domain/src/permission/interaction.rs (old interaction)
- [ ] crates/forge_domain/src/permission/request.rs (old request types)
- [ ] crates/forge_domain/src/permission/state.rs (old state management)
- [ ] crates/forge_domain/src/permission/storage.rs (old storage)
- [ ] crates/forge_domain/src/permission/types.rs (old types)

Files to Create:
- [ ] crates/forge_domain/src/permission/core.rs (new permission types)
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

pub struct GlobalConfig {
    default_policy: Policy,
    permissions: HashMap<Permission, Policy>,
    deny_patterns: Vec<String>,
}
```

Files to Update:
- [ ] crates/forge_domain/src/permission/mod.rs (export new types)
- [ ] crates/forge_domain/src/lib.rs (update exports)

Example prompt:
```
<task>
Phase 1: Core Permission Types
1. Review onboarding.md and service.md
2. Delete specified old permission files
3. Create core.rs with new types
4. Update mod.rs and lib.rs exports
5. Add comprehensive tests
6. Request review
</task>
```

### 2. Configuration Format
Files to Delete:
- [ ] crates/forge_domain/src/permission/config_loader.rs (old config)
- [ ] crates/forge_domain/src/permission/config.rs (old config types)

Files to Create:
- [ ] crates/forge_domain/src/permission/config/mod.rs (new config)
- [ ] crates/forge_domain/src/permission/config/schema.rs (YAML schema)
- [ ] crates/forge_domain/src/permission/config/parser.rs (YAML parser)
- [ ] examples/permissions/basic.yml (example config)
```yaml
default_policy: session

permissions:
  read: always
  write: session
  execute: once

deny_patterns:
  - "**/secrets/**"
```

Files to Update:
- [ ] crates/forge_domain/src/permission/mod.rs (add config exports)

### 3. Permission Service
Files to Delete:
- [ ] crates/forge_tool/src/permission/service.rs (old service)
- [ ] crates/forge_tool/src/permission/manager.rs (old manager)
- [ ] crates/forge_tool/src/permission/state_manager.rs (old state)

Files to Create:
- [ ] crates/forge_tool/src/permission/service/mod.rs (new service)
```rust
pub struct PermissionService {
    config: GlobalConfig,
    cwd: PathBuf,
    session_cache: HashMap<Permission, bool>,
}
```
- [ ] crates/forge_tool/src/permission/service/checker.rs (permission checks)

Files to Update:
- [ ] crates/forge_tool/src/lib.rs (update service exports)
- [ ] crates/forge_tool/src/permission/mod.rs (update exports)

### 4. Storage Implementation
Files to Delete:
- [ ] crates/forge_tool/src/permission/storage/session.rs
- [ ] crates/forge_tool/src/permission/storage/config.rs

Files to Create:
- [ ] crates/forge_tool/src/permission/storage/mod.rs (new storage)
```rust
pub struct YamlStorage {
    config_path: PathBuf,
    cache: HashMap<Permission, Policy>,
}
```
- [ ] crates/forge_tool/src/permission/storage/cache.rs (in-memory cache)

Files to Update:
- [ ] crates/forge_tool/src/permission/mod.rs (update storage exports)

### 5. CLI Integration
Files to Delete:
- [ ] crates/forge_tool/src/permission/cli.rs (old CLI)
- [ ] crates/forge_tool/src/permission/result.rs (old results)

Files to Create:
- [ ] crates/forge_tool/src/permission/cli/mod.rs (new CLI)
- [ ] crates/forge_tool/src/permission/cli/prompt.rs (user prompts)
- [ ] crates/forge_tool/src/permission/cli/display.rs (status display)

Files to Update:
- [ ] crates/forge_tool/src/lib.rs (update CLI exports)

### 6. Testing & Documentation
Files to Delete:
- [ ] All old test files in affected directories

Files to Create:
- [ ] crates/forge_tool/src/permission/tests/core_test.rs
- [ ] crates/forge_tool/src/permission/tests/config_test.rs
- [ ] crates/forge_tool/src/permission/tests/service_test.rs
- [ ] crates/forge_tool/src/permission/tests/integration_test.rs
- [ ] docs/permissions.md (new documentation)
- [ ] docs/permissions_migration.md (migration guide)

Files to Update:
- [ ] README.md (update permission section)

## Example Implementation Steps

### Step 1: Core Types
```rust
<task>
1. Delete old permission type files:
   rm crates/forge_domain/src/permission/{error,interaction,request,state,storage,types}.rs

2. Create new core.rs with simplified types:
   touch crates/forge_domain/src/permission/core.rs

3. Update mod.rs exports

4. Add tests
</task>

<agent_learning>
  <concepts>
    - Simplified permission model implementation
    - Rust module organization
  </concepts>
  <challenges>
    - Ensuring backward compatibility
    - Organizing new type hierarchy
  </challenges>
</agent_learning>

<user_feedback>
  <feedback_item date="2024-01-15">
    - Good: Clean type organization
    - Improve: Add derives for common traits
  </feedback_item>
</user_feedback>
```

## Code Organization

```
crates/forge_domain/src/permission/
├── core.rs           # Core permission types
├── config/           # Configuration handling
│   ├── mod.rs
│   ├── schema.rs
│   └── parser.rs
├── service/          # Permission service
│   ├── mod.rs
│   └── checker.rs
├── storage/          # Storage implementation
│   ├── mod.rs
│   └── cache.rs
├── cli/              # CLI integration
│   ├── mod.rs
│   ├── prompt.rs
│   └── display.rs
└── tests/            # Test files
    ├── core_test.rs
    └── integration_test.rs
```

## Review Checkpoints

After each major component:
1. All specified files are properly handled (deleted/created/updated)
2. Code follows service.md guidelines
3. Documentation is complete
4. Tests are comprehensive
5. Migration path is clear
6. All code should compile and run tests
