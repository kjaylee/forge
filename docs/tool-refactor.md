# Tool Refactor

- For each tool in forge_tool:
  - We will create a service trait in forge_domain
  - If the tool service trait needs a Result type, it should use anyhow::Result
  - The methods on tool service trait can be async (use async_trait) for such cases
  - We need to create a service implementation in forge_app
  - Add the traits to ForgeDomain
- Create a generic implementation of ToolCallService that we can use to create tools

## Phase 1: Define the relevant traits
- Create all the trait for each tool.
- Create a dir for tools and move all the traits there

## Phase 2: Use the traits to create all the tools

- This should essentially create a vec of tools like in `forge_tools/lib`
