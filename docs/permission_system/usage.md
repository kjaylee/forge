# Permission System Usage Guide

## Overview
The permission system provides file system access control for Code-Forge tools. It implements a straightforward permission model focused on basic access control and path validation.

## Core Concepts

### 1. Permission Types
The system supports four basic permission types:

- `read`: Permission to read file contents
- `write`: Permission to modify files
- `execute`: Permission to run commands or scripts
- `deny`: Access is explicitly denied

### 2. Policy Types
Each permission can be governed by one of three policies:

- `always`: Permission is always granted without asking
- `once`: Permission is granted for a single operation
- `session`: Permission is granted for the current session

### 3. Configuration Structure

Basic configuration structure in YAML:

```yaml
permission_config:
  # Default policy for unspecified permissions
  default_policy: session

  # Permission-specific policies
  permissions:
    read: always
    write: session
    execute: once

  # Patterns for denied paths
  deny_patterns:
    - "**/secrets/**"
    - "**/*.env"
```

## Configuration Details

### 1. Default Configuration

A minimal configuration provides session-level access:

```yaml
permission_config:
  default_policy: session
  permissions: {}
  deny_patterns: []
```

### 2. Path Control

The system enforces several path-related security features:
- All paths must be within the working directory
- Maximum depth restrictions prevent deep traversal
- Path existence and accessibility validation
- Pattern-based path denial

## Configuration Examples

### 1. Basic Development Setup

```yaml
permission_config:
  default_policy: session
  
  permissions:
    read: always    # Always allow reading files
    write: session  # Allow writing for the session
    execute: once   # Require approval for each execution
  
  deny_patterns:
    - "**/node_modules/**"
    - "**/target/**"
    - "**/.git/**"
```

### 2. Secure Production Setup

```yaml
permission_config:
  default_policy: once  # Default to requiring approval
  
  permissions:
    read: session
    write: once
    execute: deny    # Prevent execution entirely
  
  deny_patterns:
    # Security-sensitive files
    - "**/*.env"
    - "**/*.key"
    - "**/*.pem"
    - "**/secrets/**"
    - "**/security/**"
    
    # Build artifacts and dependencies
    - "**/node_modules/**"
    - "**/target/**"
    - "**/.git/**"
    
    # Temporary and cache files
    - "**/tmp/**"
    - "**/cache/**"
```

## Common Error Messages

When using the permission system, you may encounter these messages:

1. Path Access Denied:
```
Access denied to path: /path/to/file
```

2. Path Outside Working Directory:
```
Path outside current working directory: /some/external/path
```

3. Invalid Path:
```
Invalid path: path/does/not/exist
```

## Best Practices

1. **Path Security**
   - Use deny patterns for sensitive directories
   - Keep paths within the working directory
   - Use specific patterns rather than broad denials

2. **Permission Configuration**
   - Start with restrictive defaults
   - Grant minimal necessary permissions
   - Use deny patterns for sensitive paths

3. **Policy Usage**
   - Use `once` for sensitive operations
   - Use `session` for repeated safe operations
   - Use `always` sparingly and only for safe operations
   - Use `deny` for high-risk operations

## Deny Pattern Examples

Common patterns to consider denying:

```yaml
deny_patterns:
  # Security
  - "**/*.env"
  - "**/*.key"
  - "**/*.pem"
  - "**/secrets/**"
  - "**/security/**"
  
  # Build artifacts
  - "**/node_modules/**"
  - "**/target/**"
  - "**/dist/**"
  - "**/build/**"
  
  # Version control
  - "**/.git/**"
  - "**/.svn/**"
  
  # Temporary files
  - "**/tmp/**"
  - "**/temp/**"
  - "**/cache/**"
  
  # Logs
  - "**/logs/**"
  - "**/*.log"
  
  # System files
  - "**/.DS_Store"
  - "**/Thumbs.db"
```

## Note on Usage

The permission system focuses on basic access control and path validation through:

- Permission types (read, write, execute)
- Policy-based access control (always, once, session)
- Path pattern denial
- Working directory enforcement

Future enhancements may include:
- Directory-specific configurations
- More granular permission controls
- Enhanced pattern matching
- Additional policy types