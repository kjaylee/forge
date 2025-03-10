<!--
Tone: Maintain a professional and informative tone throughout. Ensure that explanations are clear and technical terms are used appropriately to engage a technical audience.
Best Practices:
- Use consistent terminology and formatting for commands and examples.
- Clearly highlight unique aspects of 'forge' to distinguish it from other tools.
-->

[![CI Status](https://img.shields.io/github/actions/workflow/status/antinomyhq/forge/ci.yml?style=for-the-badge)](https://github.com/antinomyhq/forge/actions)
[![GitHub Release](https://img.shields.io/github/v/release/antinomyhq/forge?style=for-the-badge)](https://github.com/antinomyhq/forge/releases)
[![Discord](https://img.shields.io/discord/1044859667798568962?style=for-the-badge&cacheSeconds=120&logo=discord)](https://discord.gg/kRZBPpkgwq)

**Forge: AI-Enhanced Terminal Development Environment**

![Code-Forge Demo](https://antinomy.ai/images/forge_demo_2x.gif)

Forge is a comprehensive coding agent that integrates AI capabilities with your development environment, offering sophisticated assistance while maintaining the efficiency of your existing workflow.

- Advanced AI coding assistant with comprehensive understanding, planning, and execution of complex development tasks
- Lightning-fast performance with sub-50ms startup times
- Seamless integration with existing Unix tools and workflows
- Context-aware assistance that understands your development environment and workflows
- Natural language interface to powerful system operations
- Enhanced security features with optional restricted shell mode
- Multi-agent architecture that orchestrates specialized AI agents to solve complex problems collaboratively
- Powered by Claude 3.7 Sonnet for state-of-the-art AI capabilities

## Quick Start

### Mac

```bash
# Add Code-Forge's package repository to Homebrew
brew tap antinomyhq/code-forge
# Install Code-Forge
brew install code-forge
```

### Linux

```bash
# Using curl
curl -L https://raw.githubusercontent.com/antinomyhq/forge/main/install.sh | bash
```

### Setup

1. Create a `.env` file in your home directory with your API credentials:

   ```bash
   # Your API key for accessing AI models
   OPENROUTER_API_KEY=<Enter your Open Router Key>
   ```

   _Get a key at [Open Router](https://openrouter.ai/)_

2. Run `forge` to start using it!

## Key Features

- **Complete Coding Agent**: Write, refactor, debug, test, and document code
- **Interactive AI Shell**: Natural language interface with shell power
- **Enhanced Security**: Optional restricted shell mode with `-r` flag
- **Operation Modes**: ACT (modify files) and PLAN (analysis only)
- **Multi-Agent Architecture**: Specialized agents work together
- **Built-in Commands**: `/new`, `/info`, `/models`, `/dump`, `/act`, `/plan`

## Documentation

For detailed documentation, check out the docs folder:

- [Full Installation Guide](docs/user/installation.md)
- [Detailed Features](docs/user/features.md)
- [Configuration Files](docs/user/configuration.md)
- [Custom Workflows](docs/user/workflows.md)
- [Provider Configuration](docs/user/providers.md)
- [Why a Shell Interface?](docs/user/why-shell.md)

## Community

Join our vibrant Discord community to connect with other Code-Forge users and contributors, get help with your projects, share ideas, and provide feedback!

[![Discord](https://img.shields.io/discord/1044859667798568962?style=for-the-badge&cacheSeconds=120&logo=discord)](https://discord.gg/kRZBPpkgwq)

## Support Us

Your support drives Code-Forge's continued evolution! By starring our GitHub repository, you:

- Help others discover this powerful tool
- Motivate our development team
- Enable us to prioritize new features
- Strengthen our open-source community

Recent community feedback has helped us implement features like improved autocomplete, cross-platform optimization, and enhanced security features. Join our growing community of developers who are reshaping the future of AI-powered development!