# Permission System Configuration Guide

The permission system uses YAML configuration files to define access policies for different operations. This guide explains how to configure the permissions for your environment.

## Configuration Location

The system looks for configuration in the following order:
1. Path specified in `FORGE_CONFIG` environment variable
2. `config.yml` in the current directory
3. Falls back to default configuration (all operations require confirmation)

## Basic Structure

The configuration file has three main sections:
- `read`: File read operations
- `write`: File write operations
- `execute`: Command execution operations

### Permission Types

Each operation can be configured with one of two types:
- `Once`: Ask for permission each time
- `Always`: Either allow all or use whitelist

### Example Configuration

```yaml
# Read operations
read:
  type: "Once"  # Ask for each read

# Write operations
write:
  type: "Once"  # Ask for each write

# Execute operations
execute:
  type: "Always"
  whitelist:
    type: "Some"  # or "All"
    commands:
      - "ls"
      - "git status"
```

## Detailed Options

### Read and Write Operations
```yaml
read:  # or write:
  type: "Once"   # Ask each time
  # or
  type: "Always" # Always allow
```

### Execute Operations
```yaml
execute:
  type: "Once"   # Ask for each command
  # or
  type: "Always"
  whitelist:
    type: "All"   # Allow all commands
  # or
  type: "Always"
  whitelist:
    type: "Some"
    commands:     # List specific allowed commands
      - "ls"
      - "git status"
```

## Command Matching

For execute permissions with a whitelist:
- Commands are matched using substring comparison
- For example, if "git" is whitelisted, all git commands will be allowed
- Be specific to avoid unintended permissions (use "git status" instead of just "git")

## Default Behavior

If no configuration is found or if there are parsing errors:
- All operations default to "Once" (ask each time)
- No commands are whitelisted
- Each operation requires explicit permission

## Security Considerations

1. Whitelist Specificity:
   - Be specific with command whitelisting
   - Use full command names when possible
   - Avoid overly broad permissions

2. File Operations:
   - Consider using "Once" for write operations
   - Use "Always" carefully with file operations

3. Configuration Protection:
   - Protect the configuration file from unauthorized modifications
   - Use version control for configuration changes
   - Review configurations regularly