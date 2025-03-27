use std::env;
use std::path::Path;
use std::sync::Arc;

use anyhow::Result;
use derive_setters::Setters;
use forge_api::{Event, ForgeAPI, API};
use forge_review_v2::XMLExtensions;
use futures::future::try_join_all;
use serde::Serialize;
use serde_json::json;

#[derive(Clone, Debug, Default, Setters, Serialize)]
#[setters(into)]
struct Verification {
    law: String,
    requirement: String,
    status: String,
}

#[tokio::main]
async fn main() -> Result<()> {
    let now = chrono::Local::now().format("%Y-%m-%d_%H-%M-%S").to_string();
    // Initialize API and load workflow configuration
    let api = Arc::new(ForgeAPI::init(false));
    let workflow = &api.load(Some(Path::new("./review.yaml"))).await?;

    // Convert relative path to absolute path
    let current_dir = env::current_dir()?;
    let input = current_dir.join(".forge").join("case-study-2");

    // Input Paths
    let product_requirements = input.join("context-compaction-prd.md");
    let pull_request_path = input.join("pull-request.diff");
    let pull_request = &tokio::fs::read_to_string(pull_request_path).await?;

    // Output Paths
    let output = current_dir.join(".forge").join(now);
    tokio::fs::create_dir_all(output.clone()).await?;

    let product_requirements = tokio::fs::read_to_string(product_requirements).await?;

    let raw_fr = api
        .run(
            workflow,
            Event::new("analyze-spec", product_requirements.clone()),
        )
        .await?;

    let requirements = raw_fr.extract_tag("requirement");

    tokio::fs::write(
        output.join("functional-requirements.md"),
        requirements.join("\n\n"),
    )
    .await?;

    let laws = try_join_all(requirements.into_iter().map(|req| {
        let product_requirements = product_requirements.clone();
        let api = api.clone();
        async move {
            let value = json!({
                "product_requirements": product_requirements.clone(),
                "functional_requirement": req
            });

            let raw_law = api
                .clone()
                .run(workflow, Event::new("generate-laws", value))
                .await?;

            let laws = raw_law.extract_tag("law");

            anyhow::Ok(
                laws.into_iter()
                    .map(|law| Verification::default().law(law).requirement(req))
                    .collect::<Vec<_>>(),
            )
        }
    }))
    .await?
    .into_iter()
    .flatten()
    .collect::<Vec<_>>();

    let verification = try_join_all(laws.into_iter().map(|verification| {
        let law = verification.law.clone();
        let api = api.clone();
        async move {
            let value = json!({
                "pull_request": pull_request.clone(),
                "law": law
            });

            let raw_verification = api
                .clone()
                .run(workflow, Event::new("verify-pr", value))
                .await?;

            anyhow::Ok(
                raw_verification
                    .extract_tag("verification")
                    .into_iter()
                    .map(|status| verification.clone().status(status))
                    .collect::<Vec<_>>(),
            )
        }
    }))
    .await?
    .into_iter()
    .flatten()
    .collect::<Vec<_>>();

    tokio::fs::write(
        output.join("verification.md"),
        verification.iter().fold(String::new(), |mut acc, s| {
            acc.push_str(format!("Requirement: {}\n", s.requirement).as_str());
            acc.push_str(format!("Status: {}\n", s.status).as_str());
            acc.push('\n');
            acc
        }),
    )
    .await?;

    let value = json!({
        "pull_request_diff": pull_request,
        "verification_status": verification
    });

    let raw_summary = api
        .run(workflow, Event::new("summarize-reports", value))
        .await?;

    let summary = raw_summary.extract_tag("summary");

    tokio::fs::write(output.join("summary.md"), summary.join("\n")).await?;

    Ok(())
}
