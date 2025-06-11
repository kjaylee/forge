---
layout: default
title: Operating Agents
parent: Features
nav_order: 6
---

# Operating Agents

Forge uses different specialized agents to provide flexible assistance based on your needs. You can switch between these agents to get the right type of help for your current task:

## Forge Agent(Default)

Forge is the default agent when you start the application and is empowered to directly implement changes to your codebase and execute commands:

- **Full Execution**: Forge can modify files, create new ones, and execute shell commands
- **Implementation**: Directly implements the solutions it proposes
- **Verification**: Performs verification steps to ensure changes work as intended
- **Best For**: When you want Forge to handle implementation details and fix issues directly

**Example**:

```bash
# Switches to Forge Agent within a session
/act

# Or use the general agent command and then from drop down select `Forge` agent
/agent
```

## Muse Agent

Muse analyzes and plans but doesn't modify your codebase:

- **Read-Only Operations**: Can only read files and run non-destructive commands
- **Detailed Analysis**: Thoroughly examines code, identifies issues, and proposes solutions
- **Structured Planning**: Provides step-by-step action plans for implementing changes
- **Best For**: When you want to understand what changes are needed before implementing them yourself

**Example**:

```bash
# Switch to Muse Agent within a session
/plan

# Or use the general agent command and then from drop down select `Muse` agent
/agent 
```

You can easily switch between agents during a session using the `/act`, `/plan`, or `/agent` commands. Muse is especially useful for reviewing potential changes before they're implemented, while Forge streamlines the development process by handling implementation details for you.