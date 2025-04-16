---
layout: default
title: Built-in Commands
parent: Features
nav_order: 4
---

# Built-in Commands

Forge offers several built-in commands to enhance your interaction:

- `/new` - Start a new task when you've completed your current one
- `/info` - View environment summary, logs folder location, and command history
- `/models` - List all available AI models with capabilities and context limits
- `/model <model_id>` - Switch to a different AI model during a conversation
- `/dump` - Save the current conversation in JSON format to a file for reference
- `/act` - Switch to ACT mode (default), allowing Forge to execute commands and implement changes
- `/plan` - Switch to PLAN mode, where Forge analyzes and plans but doesn't modify files
- `/help` - Switch to HELP mode for tool questions

## Usage

These commands can be entered directly in the Forge CLI by typing the command name preceded by a forward slash.

Examples:

```
/info
```

This will display information about your environment including:
- Operating system details
- Current working directory
- Log file location
- Application version
- Available models

```
/model claude-3-opus
```

This will switch the current conversation to use the Claude 3 Opus model for all agents.

## Switching Models

The `/model` command allows you to interactively switch between different AI models during a conversation:

1. First, use `/models` to see a list of available models and their IDs
2. Then use `/model <model_id>` to switch to your preferred model
3. All agents in the current conversation will be updated to use the specified model
4. Any new messages will be processed using the selected model

This is particularly useful when:
- You need more advanced reasoning capabilities for complex tasks
- You want to try different models to compare their responses
- You need a model with a larger context window for processing more information