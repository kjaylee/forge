# Installation

## Mac

Using Homebrew (macOS package manager):

```bash
# Add Code-Forge's package repository to Homebrew
brew tap antinomyhq/code-forge
# Install Code-Forge
brew install code-forge
```

## Linux

Choose either method to install:

```bash
# Using curl (common download tool)
curl -L https://raw.githubusercontent.com/antinomyhq/forge/main/install.sh | bash

# Or using wget (alternative download tool)
wget -qO- https://raw.githubusercontent.com/antinomyhq/forge/main/install.sh | bash
```

## Get Started

1. Create a `.env` file in your home directory with your API credentials:

   ```bash
   # Your API key for accessing AI models (see Environment Configuration section)
   OPENROUTER_API_KEY=<Enter your Open Router Key>
   
   # Optional: Set a custom URL for OpenAI-compatible providers
   #OPENAI_URL=https://custom-openai-provider.com/v1
   ```

   _You can get a Key at [Open Router](https://openrouter.ai/)_

2. Launch Code Forge:

   ![Code-Forge Demo](https://antinomy.ai/images/forge_demo_2x.gif)