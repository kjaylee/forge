use std::path::{Path, PathBuf};
use std::sync::Arc;

use anyhow::Result;
use forge_api::{ForgeAPI, API};
use forge_review_v2::prelude::*;
use forge_review_v2::steps::{AnalyzeSpec, GenerateLaws, SpecDocument, SummarizeReport};

#[tokio::main]
async fn main() -> Result<()> {
    // Initialize API and load workflow configuration
    let api = Arc::new(ForgeAPI::init(false));
    let workflow = api.load(Some(Path::new("./review.yaml"))).await?;
    let artifact_path = Path::new("./prd-verification-workflow-artifacts");

    // start the workflow
    let output = AnalyzeSpec::new(api.clone(), workflow.clone())
        .pipe(GenerateLaws::new(
            api.clone(),
            workflow.clone(),
            artifact_path.join("laws"),
        ))
        .pipe(VerifyLaws::new(
            api.clone(),
            workflow.clone(),
            artifact_path.join("verification"),
            artifact_path.join("pull-request.diff"),
        ))
        .pipe(SummarizeReport::new(
            api.clone(),
            workflow.clone(),
            artifact_path.join("pull-request.diff"),
            artifact_path.join("final-report.md"),
        ))
        .execute(WorkflowState::new(SpecDocument::new(
            PathBuf::from("./todo-mark-done-prd.md"),
            artifact_path.join("functional_requirements.md"),
        )))
        .await?;

    println!("{:#?}", output);

    Ok(())
}
