# Features

## Complete Coding Agent

Code Forge functions as a comprehensive development assistant with capabilities to:

- Write, refactor, and optimize code based on specifications
- Debug complex issues through systematic error analysis
- Generate test suites for existing codebases
- Document code and generate technical specifications
- Propose architectural improvements and optimizations

## Interactive AI Shell

Transform your command-line experience with natural language interaction while maintaining the power and flexibility of traditional shell commands.

## Enhanced Security

Code-Forge prioritizes security by providing a restricted shell mode (rbash) that limits potentially dangerous operations:

- **Flexible Security Options**: Choose between standard and restricted modes based on your needs
- **Restricted Mode**: Enable with `-r` flag to prevent potentially harmful operations
- **Standard Mode**: Uses regular shell by default (bash on Unix/Mac, cmd on Windows)
- **Security Controls**: Restricted mode prevents:
  - Changing directories
  - Setting/modifying environment variables
  - Executing commands with absolute paths
  - Modifying shell options

**Example**:

```bash
# Standard mode (default)
forge

# Restricted secure mode
forge -r
```

Additional security features include:

- Direct API connection to Open Router without intermediate servers
- Local terminal operation for maximum control and data privacy

## Built-in Commands

Forge offers several built-in commands to enhance your interaction:

- `/new` - Start a new task when you've completed your current one
- `/info` - View environment summary, logs folder location, and command history
- `/models` - List all available AI models with capabilities and context limits
- `/dump` - Save the current conversation in JSON format to a file for reference
- `/act` - Switch to ACT mode (default), allowing Forge to execute commands and implement changes
- `/plan` - Switch to PLAN mode, where Forge analyzes and plans but doesn't modify files

## Autocomplete

Boost your productivity with intelligent command completion:

- Type `@` and press Tab for contextual file/path completion
- Use Right Arrow to complete previously executed commands
- Access command history with Up Arrow
- Quick history search with Ctrl+R

## WYSIWYG Shell Experience

Enhance your interactive shell experience with WYSIWYG (What You See Is What You Get) integration. 'forge' now visualizes each command executed, complete with colorful formatting, allowing you to see command outputs just as if you were typing them directly into your terminal. This feature ensures clarity and enhances interaction, making every command visible in rich detail.

## Command Interruption

Stay in control of your shell environment with intuitive command handling:

- **Cancel with `CTRL+C`:** Gracefully interrupt ongoing operations, providing the flexibility to halt processes that no longer need execution.
- **Exit with `CTRL+D`:** Easily exit the shell session without hassle, ensuring you can quickly terminate your operations when needed.

## Operation Modes

Forge operates in two distinct modes to provide flexible assistance based on your needs:

### ACT Mode (Default)

In ACT mode, which is the default when you start Forge, the assistant is empowered to directly implement changes to your codebase and execute commands:

- **Full Execution**: Forge can modify files, create new ones, and execute shell commands
- **Implementation**: Directly implements the solutions it proposes
- **Verification**: Performs verification steps to ensure changes work as intended
- **Best For**: When you want Forge to handle implementation details and fix issues directly

**Example**:

```bash
# Switch to ACT mode within a Forge session
/act
```

### PLAN Mode

In PLAN mode, Forge analyzes and plans but doesn't modify your codebase:

- **Read-Only Operations**: Can only read files and run non-destructive commands
- **Detailed Analysis**: Thoroughly examines code, identifies issues, and proposes solutions
- **Structured Planning**: Provides step-by-step action plans for implementing changes
- **Best For**: When you want to understand what changes are needed before implementing them yourself

**Example**:

```bash
# Switch to PLAN mode within a Forge session
/plan
```

You can easily switch between modes during a session using the `/act` and `/plan` commands. PLAN mode is especially useful for reviewing potential changes before they're implemented, while ACT mode streamlines the development process by handling implementation details for you.

## Application Logs

Forge generates detailed JSON-formatted logs that help with troubleshooting and understanding the application's behavior. These logs provide valuable insights into system operations and API interactions.

**Log Location and Access**

Logs are stored in your application support directory with date-based filenames. The typical path looks like:

```bash
/Users/username/Library/Application Support/forge/logs/forge.log.YYYY-MM-DD
```

You can easily locate log files using the built-in command `/info`, which displays system information including the exact path to your log files.

**Viewing and Filtering Logs**

To view logs in real-time with automatic updates, use the `tail` command:

```bash
tail -f /Users/username/Library/Application Support/forge/logs/forge.log.2025-03-07
```

**Formatted Log Viewing with jq**

Since Forge logs are in JSON format, you can pipe them through `jq` for better readability:

```bash
tail -f /Users/username/Library/Application Support/forge/logs/forge.log.2025-03-07 | jq
```

This displays the logs in a nicely color-coded structure that's much easier to analyze, helping you quickly identify patterns, errors, or specific behavior during development and debugging.