use std::path::PathBuf;

use forge_domain::{Environment, Variables, Workflow};

use crate::WorkflowLoader;

#[derive(Clone)]
pub struct ForgeWorkflow {
    workflow: Workflow,
}

impl ForgeWorkflow {
    pub fn new(_env: Environment) -> Self {
        // TODO: remove hardcoded paths and unwraps
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let path = manifest_dir.join("fixtures").join("forge-workflow.yml");
        let workflow = WorkflowLoader::load(path).unwrap();

        Self { workflow }
    }
}

impl From<ForgeWorkflow> for Workflow {
    fn from(value: ForgeWorkflow) -> Self {
        Self {
            agents: value.workflow.agents,
            variables: Variables::default(),
        }
    }
}
