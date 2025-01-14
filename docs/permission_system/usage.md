# Permission System

## Configuration Modes

The permission system supports three primary modes for different operations:

### 1. `Once`
- Prompts for confirmation on each operation
- Useful for sensitive or infrequent actions
- Default fallback mode

### 2. `Always`
#### Global Allow
```yaml
read: Always    # Always allow without prompting
write: Always   # Always allow without prompting
```

#### Selective Whitelist
```yaml
execute:
  Always:
    Some:       # Allow only specific commands
      - "ls"
      - "git status"
      - "git diff"
```

## Example Configuration

```yaml
read: Always    # Unrestricted read access
write: Once     # Confirm before each write operation
execute:        # Selective execute permissions
  Always:
    Some:
      - "ls"
      - "git status"
      - "git diff"
```

## Interaction Flow

- For `Once` permissions: Interactive selection prompt
- For `Always` with whitelist: 
  - Automatically allow whitelisted commands
  - Prompt for non-whitelisted commands
- For `Always` global: Automatic permission granted

## Best Practices

- Use `Once` for sensitive operations
- Use whitelisting for controlled execute permissions
- Regularly review and update your permission configuration