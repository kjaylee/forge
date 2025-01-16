mod approve;
mod ask;
mod fs;
mod learning;
mod outline;
mod select;
mod shell;
mod think;

use std::sync::Arc;

use approve::Approve;
use forge_domain::{LearningRepository, Tool};
use fs::*;
use learning::Learning;
use outline::Outline;
use select::SelectTool;
use shell::Shell;
use think::Think;

pub fn tools(
    current_working_directory: String,
    learning_repository: Arc<dyn LearningRepository>,
) -> Vec<Tool> {
    vec![
        Approve.into(),
        FSRead.into(),
        FSWrite.into(),
        FSList.into(),
        FSSearch.into(),
        FSFileInfo.into(),
        FSReplace.into(),
        Outline.into(),
        SelectTool.into(),
        Shell::default().into(),
        Think::default().into(),
        Learning::new(current_working_directory, learning_repository).into(),
    ]
}
