[![CI Status](https://img.shields.io/github/actions/workflow/status/antinomyhq/forge/ci.yml?style=for-the-badge)](https://github.com/antinomyhq/forge/actions)
[![GitHub Release](https://img.shields.io/github/v/release/antinomyhq/forge?style=for-the-badge)](https://github.com/antinomyhq/forge/releases)

**Imagine having a brilliant AI coding partner right in your terminal** — one that doesn't just respond to commands but actively helps you solve complex development problems, write code, debug issues, and automate repetitive tasks.

Code Forge is a complete coding agent that transforms how developers work. It combines the power of state-of-the-art AI with deep integration into your development environment.

- **Full-Fledged Coding Agent** — Not just a shell: a partner that can understand, plan, and execute complex coding tasks
- **Blazing Fast** — Starts in under 50ms, so you never lose your flow
- **Works With Your Tools** — Seamlessly integrates with your favorite Unix tools and existing workflows
- **Understands Your Codebase** — Analyzes context across files, project structure, and dependencies to offer intelligent solutions
- **Natural Language Coding** — Turn plain English descriptions into working code, tests, and documentation
- **Enhanced Security** — Optional restricted shell mode for sensitive environments
- **Powered by Claude 3.7 Sonnet** — Leverages one of the most capable AI models for programming tasks

**Table of Contents**

- [Quick Install](#quick-install)
  - [Mac](#mac)
  - [Linux](#linux)
- [Get Started in 30 Seconds](#get-started-in-30-seconds)
- [See It In Action](#see-it-in-action)
- [Powerful Features](#powerful-features)
  - [Complete Coding Agent](#complete-coding-agent)
  - [Interactive AI Shell](#interactive-ai-shell)
  - [Enhanced Security](#enhanced-security)
  - [Autocomplete](#autocomplete)
  - [WYSIWYG Shell Experience](#wysiwyg-shell-experience)
  - [Seamless Control](#seamless-control)
- [Why Shell?](#why-shell)
- [❤️ Support Code Forge](#️-support-code-forge)

## Quick Install

### Mac

```bash
# One command to get started
brew tap antinomyhq/code-forge && brew install code-forge
```

### Linux

```bash
# Quick install with curl
curl -L https://raw.githubusercontent.com/antinomyhq/forge/main/install.sh | bash
```

## Get Started in 30 Seconds

1. Set up your API key (one-time step):

   ```bash
   # Create a .env file in your home directory
   echo "OPEN_ROUTER_KEY=<your-key-here>" > ~/.env
   ```

   _Need a key? Get one at [Open Router](https://openrouter.ai/)_

2. Launch Code Forge:
   ```bash
   forge
   ⚡ # Now just describe what you want to build or solve!
   ```

## See It In Action

Instead of manually coding tedious tasks, let Code Forge handle them:

```bash
⚡ forge Task 1
```

<!-- <Video here> -->

```bash
⚡ forge Task 2
```

<!-- <Video here> -->

```bash
⚡ forge Task 3
```

<!-- <Video here> -->

## Powerful Features

### Complete Coding Agent

Much more than a shell - Code Forge understands your entire development environment and can:

- Write, refactor, and optimize code based on your requirements
- Debug complex issues by analyzing error patterns
- Generate tests for your codebase
- Document code and create technical specifications
- Propose architecture improvements

### Interactive AI Shell

Transform your command-line experience with natural language interaction while maintaining the power and flexibility of traditional shell commands.

### Enhanced Security

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

### Autocomplete

Boost your productivity with intelligent command completion:

- Type `@` and press Tab for contextual file/path completion
- Use Right Arrow to complete previously executed commands
- Access command history with Up Arrow
- Quick history search with Ctrl+R

### WYSIWYG Shell Experience

Enhance your interactive shell experience with WYSIWYG (What You See Is What You Get) integration. 'forge' now visualizes each command executed, complete with colorful formatting, allowing you to see command outputs just as if you were typing them directly into your terminal. This feature ensures clarity and enhances interaction, making every command visible in rich detail.

### Seamless Control

Stay in control of your shell environment with intuitive command handling:

- **Cancel with `CTRL+C`:** Gracefully interrupt ongoing operations, providing the flexibility to halt processes that no longer need execution.
- **Exit with `CTRL+D`:** Easily exit the shell session without hassle, ensuring you can quickly terminate your operations when needed.

## Why Shell?

There's a reason why the shell stood the test of time for all dev tools and still remains a cornerstone of development environments across the globe: it's fast, versatile, and seamlessly integrated with the system. The shell is where we navigate code, run tests, manage processes, and orchestrate our development environments, providing an unmatched level of control and productivity.

**Why a shell-based AI assistant like Code-Forge makes sense:**

Code Forge combines the power of AI with the command line to create a development experience that's greater than the sum of its parts:

- **Rich Tool Ecosystem**: The shell gives you immediate access to powerful Unix tools (grep, awk, sed, find) that LLMs already understand deeply. This means the AI can leverage `ripgrep` for code search, `jq` for JSON processing, `git` for version control, and hundreds of other battle-tested tools without reinventing them.

- **Context is Everything**: Your shell session already has your complete development context - current directory, project structure, environment variables, installed tools, and system state. This rich context makes the AI interactions more accurate and relevant.

- **Speed Matters**: Unlike IDEs and Web UI, Code Forge's shell is extremely light weight. This exceptional speed unlocks powerful capabilities that directly enhance your productivity: seamlessly get in and out of workflows, managing multiple feature developments in parallel, effortlessly coordinate across git worktrees, and instantly access AI assistance in any directory.

- **Tool Composition**: Unix philosophy teaches us to make tools that compose well. The AI can pipe commands together, combining tools like `find | xargs forge -p | grep "foo"` in ways that solve complex problems elegantly.

## ❤️ Support Code Forge

Your support drives Code-Forge's continued evolution! By starring our GitHub repository, you:

- Help others discover this powerful tool
- Motivate our development team
- Enable us to prioritize new features
- Strengthen our open-source community

Recent community feedback has helped us implement features like improved autocomplete, cross-platform optimization, and enhanced security features. Join our growing community of developers who are reshaping the future of AI-powered development!
