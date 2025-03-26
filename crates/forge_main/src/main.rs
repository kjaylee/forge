use std::{
    path::{Path, PathBuf},
    sync::Arc,
};

use anyhow::Result;
use forge_api::{ForgeAPI, API};
use forge_review_v2::{
    prelude::*,
    steps::{AnalyzeSpec, GenerateLaws, SpecDocument},
};

#[tokio::main]
async fn main() -> Result<()> {
    // Initialize API and load workflow configuration
    let api = Arc::new(ForgeAPI::init(false));
    let path = Path::new("./review.yaml");
    let workflow = api.load(Some(path)).await?;
    let artifact_path = Path::new("./prd-verification-workflow-artifacts");

    let output = AnalyzeSpec::new(api.clone(), workflow.clone())
        .then(GenerateLaws::new(
            api.clone(),
            workflow.clone(),
            artifact_path.join("laws"),
        ))
        .then(VerifyLaws::new(
            api.clone(),
            workflow.clone(),
            artifact_path.join("verification"),
            artifact_path.join("pull-request.diff"),
        ))
        .execute(WorkflowState::new(SpecDocument::new(
            PathBuf::from("./todo-mark-done-prd.md"),
            artifact_path.join("functional_requirements.md"),
        )))
        .await?;

    println!("{:#?}", output);

    Ok(())
}
