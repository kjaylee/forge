---
layout: home
title: Home
nav_order: 1
description: "Documentation for the Code-Forge AI-powered coding assistant platform"
permalink: /
---

# Code-Forge Documentation

Welcome to the Code-Forge documentation site. Code-Forge is a sophisticated AI-powered coding assistant platform built in Rust, designed to provide intelligent code generation, manipulation, and analysis capabilities through a modular and extensible architecture.

## Getting Started

To learn more about Code-Forge, explore the following sections:

- [Onboarding Guide](onboarding.html) - Get started with Code-Forge and learn about its system architecture
- [Development Guidelines](guidelines.html) - Best practices for developing with Code-Forge
- [Service Documentation](service.html) - Implementation details for services in Code-Forge

## User Documentation

For end-user documentation, see:

- [User Guide](user/) - Detailed user documentation
  - [Installation](user/installation.html) - How to install Forge
  - [Features](user/features.html) - Detailed explanation of features
  - [Configuration Files](user/configuration.html) - Working with configuration files
  - [Custom Workflows](user/workflows.html) - Creating custom workflows
  - [Provider Configuration](user/providers.html) - Configuring AI providers
  - [Why Shell?](user/why-shell.html) - Why a shell-based AI assistant makes sense

## Features

Code-Forge provides several powerful features:

1. **File System Operations**
   - Read/Write capabilities
   - Directory listing
   - File search with regex support
   - Smart file replacement with diff blocks
   - Code validation for multiple languages

2. **Code Analysis**
   - Language-aware code parsing
   - Function and class outline generation
   - Support for Rust, JavaScript, and Python
   - Syntax validation

3. **Conversation Management**
   - Persistent conversations
   - Context management
   - Title generation
   - History tracking

4. **Tool Framework**
   - Extensible tool system
   - JSON schema-based tool definitions
   - Asynchronous tool execution
   - Error handling and validation