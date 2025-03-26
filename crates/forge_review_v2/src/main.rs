use std::env;
use std::path::Path;
use std::sync::Arc;

use anyhow::Result;
use forge_api::{Event, ForgeAPI, API};
use forge_review_v2::XMLExtensions;

#[tokio::main]
async fn main() -> Result<()> {
    // Initialize API and load workflow configuration
    let api = Arc::new(ForgeAPI::init(false));
    let workflow = api.load(Some(Path::new("./review.yaml"))).await?;

    // Convert relative path to absolute path
    let current_dir = env::current_dir()?;
    let input = current_dir.clone();

    // Input Paths
    let product_requirements = input.join("todo-mark-done-prd.md");
    // let pull_request_path = input.join("pull-request.diff");

    // Output Paths
    // let output = current_dir.join(".forge");
    // let product_requirements_summary = current_dir.join("todo-mark-done-prd-summary.md");
    // let laws_dir = output.join("laws");
    // let verifications_dir = output.join("verifications");
    // let functional_requirement_path = output.join("functional_requirements.md");
    // let final_report_path = output.join("final-report.md");

    let product_requirements = tokio::fs::read_to_string(product_requirements).await?;

    let raw_fr = api
        .run(&workflow, Event::new("analyze-spec", product_requirements))
        .await?;

    let requirements = raw_fr.extract_tag("requirement");

    for req in requirements.iter() {}

    println!("{:#?}", requirements);

    Ok(())
}
