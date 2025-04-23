use std::sync::Arc;

use forge_domain::Tool;

use super::completion::Completion;
use super::fetch::Fetch;
use super::followup::Followup;
use super::fs::*;
use super::patch::*;
use super::shell::Shell;
use crate::Infrastructure;

pub struct ToolRegistry<F> {
    infra: Arc<F>,
}

impl<F: Infrastructure> ToolRegistry<F> {
    pub fn new(infra: Arc<F>) -> Self {
        Self { infra }
    }

    /// Returns all available tools configured with the given infrastructure
    pub fn tools(&self) -> Vec<Tool> {
        vec![
            FSRead::new(self.infra.clone()).into(),
            FSWrite::new(self.infra.clone()).into(),
            FSRemove::new(self.infra.clone()).into(),
            FSList::default().into(),
            FSFind::new(self.infra.clone()).into(),
            FSFileInfo.into(),
            FsUndo::new(self.infra.clone()).into(),
            ApplyPatchJson::new(self.infra.clone()).into(),
            Shell::new(self.infra.clone()).into(),
            Fetch::default().into(),
            Completion.into(),
            Followup::new(self.infra.clone()).into(),
        ]
    }
}

#[cfg(test)]
pub mod tests {

    use forge_domain::ToolUsagePrompt;
    use insta::assert_snapshot;

    use super::*;

    #[test]
    fn test_tool_description_length() {
        const MAX_DESCRIPTION_LENGTH: usize = 1024;

        println!("\nTool description lengths:");

        let mut any_exceeded = false;
        let stub = Arc::new(crate::infra::stub::Stub::default());
        let registry = ToolRegistry::new(stub.clone());
        for tool in registry.tools() {
            let desc_len = tool.definition.description.len();
            println!(
                "{:?}: {} chars {}",
                tool.definition.name,
                desc_len,
                if desc_len > MAX_DESCRIPTION_LENGTH {
                    "(!)"
                } else {
                    ""
                }
            );

            if desc_len > MAX_DESCRIPTION_LENGTH {
                any_exceeded = true;
            }
        }

        assert!(
            !any_exceeded,
            "One or more tools exceed the maximum description length of {}",
            MAX_DESCRIPTION_LENGTH
        );
    }

    #[test]
    fn test_tool_usage() {
        let stub = Arc::new(crate::infra::stub::Stub::default());
        let registry = ToolRegistry::new(stub.clone());
        let tools = registry
            .tools()
            .into_iter()
            .map(|tool| ToolUsagePrompt::from(tool.definition))
            .fold(String::new(), |mut acc, tool| {
                acc.push_str("\n\n");
                acc.push_str(&tool.to_string());
                acc
            });

        assert_snapshot!(tools)
    }
}
