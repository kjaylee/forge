use std::env;
use std::path::Path;
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

    // Convert relative path to absolute path
    let current_dir = env::current_dir()?;
    let artifact_path = current_dir.join(".forge");
    // files avail at root level.
    let spec_path = current_dir.join("todo-mark-done-prd.md");
    let spec_summary_path = current_dir.join("todo-mark-done-prd-summary.md");
    let pull_request_path = current_dir.join("pull-request.diff");

    // paths
    let laws_dir = artifact_path.join("laws");
    let verifications_dir = artifact_path.join("verifications");
    let functional_requirement_path = artifact_path.join("functional_requirements.md");
    let final_report_path = artifact_path.join("final-report.md");

    // start the workflow
    let _ = AnalyzeSpec::new(api.clone(), workflow.clone())
        .pipe(GenerateLaws::new(api.clone(), workflow.clone(), laws_dir))
        .pipe(VerifyLaws::new(
            api.clone(),
            workflow.clone(),
            verifications_dir,
            pull_request_path.clone(),
        ))
        .pipe(SummarizeReport::new(
            api.clone(),
            workflow.clone(),
            pull_request_path,
            final_report_path,
        ))
        .execute(WorkflowState::new(SpecDocument::new(
            spec_path,
            functional_requirement_path,
            spec_summary_path,
        )))
        .await?;

    println!(
        "Review of spec completed successfully and can be found at {} ",
        artifact_path.join("final-report.md").display()
    );

    Ok(())
}
