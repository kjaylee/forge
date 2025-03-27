use std::{env, path::PathBuf};
use std::sync::Arc;

use anyhow::Result;
use clap::Parser;
use derive_setters::Setters;
use forge_api::{Event, ForgeAPI, API};
use forge_review_v2::XMLExtensions;
use futures::future::try_join_all;
use serde::Serialize;
use serde_json::json;

// Reference to the UI module in ui.rs
mod ui;
use ui::UI;

/// CLI tool for reviewing code changes against product requirements
#[derive(Parser, Debug)]
struct Cli {
    /// Path to the pull request diff file
    #[arg(short = 'r', long)]
    pull_request_path: PathBuf,

    /// Path to the product requirements document
    #[arg(short = 'p', long)]
    product_requirement_path: PathBuf,

    /// Path to the workflow configuration file
    #[arg(short = 'w', long)]
    workflow_path: PathBuf,
}

#[derive(Clone, Debug, Default, Setters, Serialize)]
#[setters(into)]
struct Verification {
    law: String,
    requirement: String,
    status: String,
}

#[tokio::main]
async fn main() -> Result<()> {
    // Parse command line arguments
    let args = Cli::parse();
    let now = chrono::Local::now().format("%Y-%m-%d_%H-%M-%S").to_string();

    // Initialize the UI
    let ui = UI::new();
    let workflow_spinner = ui.create_spinner(
        "Loading".to_string(),
        "Initializing workflow configuration...".to_string(),
    );

    // Initialize API and load workflow configuration
    let api = Arc::new(ForgeAPI::init(false));
    let workflow = &api.load(Some(&args.workflow_path)).await?;
    ui.complete_spinner(
        &workflow_spinner,
        "Workflow configuration loaded successfully".to_string(),
    );

    // Input Paths from command line arguments
    let files_spinner =
        ui.create_spinner("Reading".to_string(), "Loading input files...".to_string());
    let pull_request = &tokio::fs::read_to_string(&args.product_requirement_path).await?;
    let product_requirements = tokio::fs::read_to_string(&args.pull_request_path).await?;
    ui.complete_spinner(
        &files_spinner,
        "Input files loaded successfully".to_string(),
    );

    // Output Paths
    let current_dir = env::current_dir()?;
    let output = current_dir.join(".forge").join(now);

    // Create the output directory
    tokio::fs::create_dir_all(output.clone()).await?;

    // Analyze specification
    let analyze_spinner = ui.create_spinner(
        "Analyzing".to_string(),
        "Processing product requirement specifications...".to_string(),
    );
    let raw_fr = api
        .run(
            workflow,
            Event::new("analyze-spec", product_requirements.clone()),
        )
        .await?;

    let requirements = raw_fr.extract_tag("requirement");
    let requirements_count = requirements.len();
    ui.complete_spinner(
        &analyze_spinner,
        format!("Discovered {} functional requirements", requirements_count),
    );

    tokio::fs::write(
        output.join("functional-requirements.md"),
        requirements.join("\n\n"),
    )
    .await?;

    // Generate laws from requirements
    let laws_main_spinner = ui.create_spinner(
        "Processing".to_string(),
        format!("Processing 0/{} requirements...", requirements_count),
    );
    let completed_reqs = Arc::new(std::sync::atomic::AtomicUsize::new(0));

    let laws = try_join_all(requirements.into_iter().map(|req| {
        let product_requirements = product_requirements.clone();
        let api = api.clone();
        let laws_main_spinner = laws_main_spinner.clone();
        let completed_reqs = completed_reqs.clone();

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

            // Increment the completed count and update spinner
            let completed = completed_reqs.fetch_add(1, std::sync::atomic::Ordering::SeqCst) + 1;
            laws_main_spinner.set_message(format!(
                "Completed {}/{} requirements",
                completed, requirements_count
            ));

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
    ui.complete_spinner(
        &laws_main_spinner,
        format!("All {} requirements processed.", requirements_count),
    );

    // Main progress indicator for verification
    let verify_main_spinner = ui.create_spinner(
        "Verifying".to_string(),
        format!("Completed 0/{} laws...", laws.len()),
    );
    let laws_count = laws.len();
    let completed_laws = Arc::new(std::sync::atomic::AtomicUsize::new(0));

    let verification = try_join_all(laws.into_iter().map(|verification| {
        let law = verification.law.clone();
        let api = api.clone();
        let verify_main_spinner = verify_main_spinner.clone();
        let completed_laws = completed_laws.clone();

        async move {
            let value = json!({
                "pull_request": pull_request.clone(),
                "law": law
            });

            let raw_verification = api
                .clone()
                .run(workflow, Event::new("verify-pr", value))
                .await?;

            let result = raw_verification
                .extract_tag("verification")
                .into_iter()
                .map(|status| verification.clone().status(status))
                .collect::<Vec<_>>();

            // Increment the completed count and update spinner
            let completed = completed_laws.fetch_add(1, std::sync::atomic::Ordering::SeqCst) + 1;
            verify_main_spinner.set_message(format!("Completed {}/{} laws", completed, laws_count));

            anyhow::Ok(result)
        }
    }))
    .await?
    .into_iter()
    .flatten()
    .collect::<Vec<_>>();
    ui.complete_spinner(
        &verify_main_spinner,
        format!("All {} laws verified against pull request", laws_count),
    );

    tokio::fs::write(
        output.join("verification.md"),
        verification.iter().fold(String::new(), |mut acc, s| {
            acc.push_str(format!("## {}\n", s.requirement).as_str());
            acc.push_str(format!("Status: {}\n", s.status).as_str());
            acc.push('\n');
            acc
        }),
    )
    .await?;

    // Generate summary
    let summary_spinner = ui.create_spinner(
        "Summarizing".to_string(),
        "Creating summary from verification results...".to_string(),
    );
    let value = json!({
        "pull_request_diff": pull_request,
        "verification_status": verification
    });

    let raw_summary = api
        .run(workflow, Event::new("summarize-reports", value))
        .await?;

    let summary = raw_summary.extract_tag("summary");

    tokio::fs::write(output.join("summary.md"), summary.join("\n")).await?;
    
    ui.complete_spinner(&summary_spinner, format!("Summary of {} verifications completed", verification.len()));
    
    Ok(())
}
