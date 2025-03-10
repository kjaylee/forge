# Custom Workflows and Multi-Agent Systems

For complex tasks, a single agent may not be sufficient. Forge allows you to create custom workflows with multiple specialized agents working together to accomplish sophisticated tasks.

## Creating Custom Workflows

You can configure your own workflows by creating a YAML file and pointing to it with the `-w` flag:

```bash
forge -w /path/to/your/workflow.yaml
```

## Workflow Configuration

A workflow consists of agents connected via events. Each agent has specific capabilities and can perform designated tasks.

### Event System

Agents communicate through events which they can publish and subscribe to:

**Built-in Events**

- `user_task_init` - Published when a new task is initiated
- `user_task_update` - Published when follow-up instructions are provided by the user

### Agent Tools

Each agent needs tools to perform tasks, configured in the `tools` field:

**Built-in Tools**

- `tool_forge_fs_read` - Read from the filesystem
- `tool_forge_fs_create` - Create or overwrite files
- `tool_forge_fs_remove` - Remove files
- `tool_forge_fs_search` - Search for patterns in files
- `tool_forge_fs_list` - List files in a directory
- `tool_forge_fs_info` - Get file metadata
- `tool_forge_process_shell` - Execute shell commands
- `tool_forge_process_think` - Perform internal reasoning
- `tool_forge_net_fetch` - Fetch data from the internet
- `tool_forge_event_dispatch` - Dispatch events to other agents
- `tool_forge_fs_patch` - Patch existing files

### Agent Configuration Options

- `id` - Unique identifier for the agent
- `model` - AI model to use (from the `\models` list)
- `tools` - List of tools the agent can use
- `subscribe` - Events the agent listens to
- `ephemeral` - If true, agent is destroyed after task completion
- `tool_supported` - (Optional) Boolean flag that determines whether tools defined in the agent configuration are actually made available to the LLM. When set to `false`, tools are listed in the configuration but not included in AI model requests, causing the agent to format tool calls in XML rather than in the model's native format. Default: `true`.
- `system_prompt` - (Optional) Instructions for how the agent should behave. While optional, it's recommended to provide clear instructions for best results.
- `user_prompt` - (Optional) Format for user inputs. If not provided, the raw event value is used.

### Built-in Templates

Forge provides templates to simplify system prompt creation:

- `system-prompt-engineer.hbs` - Template for engineering tasks
- `system-prompt-title-generator.hbs` - Template for generating descriptive titles
- `system-prompt-advocate.hbs` - Template for user advocacy and explanation
- `partial-tool-information.hbs` - Tool documentation for agents
- `partial-tool-examples.hbs` - Usage examples for tools

Use these templates with the syntax: `{{> name-of-the-template.hbs }}`

### Example Workflow Configuration

```yaml
variables:
  models:
    advanced_model: &advanced_model anthropic/claude-3.7-sonnet
    efficiency_model: &efficiency_model anthropic/claude-3.5-haiku

agents:
  - id: title_generation_worker
    model: *efficiency_model
    tools:
      - tool_forge_event_dispatch
    subscribe:
      - user_task_init
    tool_supported: false # Force XML-based tool call formatting
    system_prompt: "{{> system-prompt-title-generator.hbs }}"
    user_prompt: <technical_content>{{event.value}}</technical_content>

  - id: developer
    model: *advanced_model
    tools:
      - tool_forge_fs_read
      - tool_forge_fs_create
      - tool_forge_fs_remove
      - tool_forge_fs_patch
      - tool_forge_process_shell
      - tool_forge_net_fetch
      - tool_forge_fs_search
    subscribe:
      - user_task_init
      - user_task_update
    ephemeral: false
    tool_supported: true # Use model's native tool call format (default)
    system_prompt: "{{> system-prompt-engineer.hbs }}"
    user_prompt: |
      <task>{{event.value}}</task>
```

This example workflow creates two agents:

1. A title generation worker that creates meaningful titles for user conversations
2. A developer agent that can perform comprehensive file and system operations