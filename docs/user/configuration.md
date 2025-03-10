# Configuration Files

Forge uses YAML configuration files to define workflows that orchestrate AI agents and their interactions.

## Loading Strategy

Workflow configurations are loaded with the following priority:

1. **Custom Path**: Via `-w` flag (`forge -w /path/to/workflow.yaml`)
2. **Project Configuration**: `forge.yaml` in the current directory
3. **Default Configuration**: Built-in fallback when no configuration is found

## Basic Structure

Workflow files define agents and their orchestration:

```yaml
variables:           # Global variables 
  mode: ACT          # Default operation mode

agents:              # List of agents in the workflow
  - id: agent-name   # Unique identifier
    model: model-id  # AI model to use
    tools:           # Tools the agent can access
      - tool_forge_fs_read
      - tool_forge_process_shell
```

Project-specific `forge.yaml` files let you customize workflows for different development environments.