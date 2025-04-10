[![CI Status](https://img.shields.io/github/actions/workflow/status/antinomyhq/forge/ci.yml?style=for-the-badge)](https://github.com/antinomyhq/forge/actions)
[![GitHub Release](https://img.shields.io/github/v/release/antinomyhq/forge?style=for-the-badge)](https://github.com/antinomyhq/forge/releases)
[![Discord](https://img.shields.io/discord/1044859667798568962?style=for-the-badge&cacheSeconds=120&logo=discord)](https://discord.gg/kRZBPpkgwq)
[![CLA assistant](https://cla-assistant.io/readme/badge/antinomyhq/forge?style=for-the-badge)](https://cla-assistant.io/antinomyhq/forge)

# ⚒️ Forge: AI-Enhanced Terminal Development Environment

![Code-Forge Demo](https://assets.antinomy.ai/images/forge_demo_2x.gif)

Forge is a comprehensive coding agent that integrates AI capabilities with your development environment, offering sophisticated assistance while maintaining the efficiency of your existing workflow. ✨

## 🚀 Installation

Install Forge globally using npm:

```bash
npm install -g @antinomyhq/forge
```

Or run directly without installation using npx:

```bash
npx @antinomyhq/forge
```

This method works on **Windows**, **macOS**, and **Linux**, providing a consistent installation experience across all platforms.

## 🏁 Get Started

Forge supports multiple AI providers. Here's how to connect with each:

### Open Router

1. Create a `.env` file in your home directory with your API credentials:

   ```bash
   # .env file
   OPENROUTER_API_KEY=<your_openrouter_api_key>
   ```

2. Create a `forge.yaml` file and set the model field:

   ```yaml
   # forge.yaml
   model: anthropic/claude-3.7-sonnet # Recommended model
   ```

### OpenAI

1. Create a `.env` file in your home directory with your API credentials:

   ```bash
   # .env file
   OPENAI_API_KEY=<your_openai_api_key>
   ```

2. Create a `forge.yaml` file and set the model field:

   ```yaml
   # forge.yaml
   model: o3-mini-high # Recommended model
   ```

### OpenAI Compatible Provider

1. Create a `.env` file in your home directory with your API credentials:

   ```bash
   # .env file
   OPENAI_API_KEY=<your_provider_api_key>
   OPENAI_URL=<your_provider_url>
   ```

2. Create a `forge.yaml` file and set the model field:

   ```yaml
   # forge.yaml
   model: <sonnet series preferred model>
   ```

### Google Vertex AI

1. Create a `.env` file in your home directory with your API credentials:

   ```bash
   # .env file
   PROJECT_ID=<your_project_id>
   LOCATION=<your_location>
   OPENAI_API_KEY=<vertex_ai_key>
   OPENAI_URL=https://${LOCATION}-aiplatform.googleapis.com/v1beta1/projects/${PROJECT_ID}/locations/${LOCATION}/endpoints/openapi
   ```

2. Create a `forge.yaml` file and set the model field:

   ```yaml
   # forge.yaml
   model: google/claude-sonnet-3.7 # Recommended model
   ```

### Anthropic

1. Create a `.env` file in your home directory with your API credentials:

   ```bash
   # .env file
   ANTHROPIC_API_KEY=<your_anthropic_api_key>
   ```

2. Create a `forge.yaml` file and set the model field:

   ```yaml
   # forge.yaml
   model: claude-3-opus # Recommended model
   ```

### Amazon Bedrock

1. Create a `.env` file in your home directory with your API credentials:

   ```bash
   # .env file
   AWS_ACCESS_KEY_ID=<your_aws_access_key>
   AWS_SECRET_ACCESS_KEY=<your_aws_secret_key>
   AWS_REGION=<your_aws_region>  # e.g., us-west-2
   ```

2. Create a `forge.yaml` file and set the model field:

   ```yaml
   # forge.yaml
   model: anthropic.claude-3-opus # Recommended model
   ```

## 📚 Documentation

For comprehensive documentation on all features and capabilities, please visit the [documentation site](https://github.com/antinomyhq/forge/tree/main/docs).

## 🤝 Community

Join our vibrant Discord community to connect with other Code-Forge users and contributors, get help with your projects, share ideas, and provide feedback! 🌟

[![Discord](https://img.shields.io/discord/1044859667798568962?style=for-the-badge&cacheSeconds=120&logo=discord)](https://discord.gg/kRZBPpkgwq)

## ⭐ Support Us

Your support drives Code-Forge's continued evolution! By starring our GitHub repository, you:

- Help others discover this powerful tool 🔍
- Motivate our development team 💪
- Enable us to prioritize new features 🛠️
- Strengthen our open-source community 🌱