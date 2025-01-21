mod approve;
mod ask;
mod fetch;
mod fs;
mod learning;
mod outline;
mod patch;
mod select;
mod shell;
mod syn;
mod think;

use std::sync::Arc;

use approve::Approve;
use fetch::Fetch;
use forge_domain::{EmbeddingsRepository, Tool};
use fs::*;
use learning::Learning;
use outline::Outline;
use patch::ApplyPatch;
use select::SelectTool;
use shell::Shell;
use think::Think;

pub fn tools(learning_embedding_idx: Arc<dyn EmbeddingsRepository>) -> Vec<Tool> {
    vec![
        Approve.into(),
        FSRead.into(),
        FSWrite.into(),
        FSList.into(),
        FSSearch.into(),
        FSFileInfo.into(),
        ApplyPatch.into(),
        Outline.into(),
        SelectTool.into(),
        Shell::default().into(),
        Think::default().into(),
        Fetch::default().into(),
        Learning::new(learning_embedding_idx).into(),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use learning::tests::MockEmbeddingsRepository;

    #[test]
    fn test_tool_description_length() {
        const MAX_DESCRIPTION_LENGTH: usize = 1024;

        println!("\nTool description lengths:");

        let mut any_exceeded = false;
        for tool in tools(Arc::new(MockEmbeddingsRepository::default())) {
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
}
