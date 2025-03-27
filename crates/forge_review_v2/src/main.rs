use std::env;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;

use anyhow::Result;
use clap::Parser;
use derive_setters::Setters;
use forge_api::{Event, ForgeAPI, API};
use forge_review_v2::XMLExtensions;
use futures::future::try_join_all;
use indicatif::{ProgressBar, ProgressStyle, MultiProgress};
use serde::Serialize;
use serde_json::json;

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
    // Initialize API and load workflow configuration
    let api = Arc::new(ForgeAPI::init(false));
    
    // Setup progress indicators
    let multi_progress = Arc::new(MultiProgress::new());
    
    // Function to create spinner and completion styles
    let create_spinner_style = || -> ProgressStyle {
        ProgressStyle::default_spinner()
            .tick_chars("⣾⣽⣻⢿⡿⣟⣯⣷")
            .template("{prefix:>12.cyan} {spinner:.blue} {wide_msg}")
            .unwrap()
    };
    
    let create_completion_style = || -> ProgressStyle {
        ProgressStyle::default_spinner()
            .template("{prefix:>12.cyan} {wide_msg}")
            .unwrap()
    };
    
    // Success prefix - will be used for completed tasks
    let success_prefix = "\x1b[32m✓\x1b[0m";  // Green checkmark with color reset
    
    // Create a spinner for workflow loading
    let workflow_spinner = multi_progress.add(ProgressBar::new_spinner());
    workflow_spinner.set_style(create_spinner_style());
    workflow_spinner.set_prefix("Loading");
    workflow_spinner.enable_steady_tick(Duration::from_millis(80));
    workflow_spinner.set_message("Initializing workflow configuration...");
    
    let workflow = &api.load(Some(&args.workflow_path)).await?;
    workflow_spinner.set_prefix(success_prefix);
    workflow_spinner.set_style(create_completion_style());
    workflow_spinner.finish_with_message("Workflow configuration loaded successfully");

    // Convert relative path to absolute path
    let current_dir = env::current_dir()?;

    // Input Paths from command line arguments
    let product_requirements_path = &args.product_requirement_path;
    let pull_request_path = &args.pull_request_path;
    
    // Create spinners for file reading
    let files_spinner = multi_progress.add(ProgressBar::new_spinner());
    files_spinner.set_style(create_spinner_style());
    files_spinner.set_prefix("Reading");
    files_spinner.enable_steady_tick(Duration::from_millis(80));
    files_spinner.set_message("Loading input files...");
    
    let pull_request = &tokio::fs::read_to_string(pull_request_path).await?;
    let product_requirements = tokio::fs::read_to_string(product_requirements_path).await?;
    
    files_spinner.set_prefix(success_prefix);
    files_spinner.set_style(create_completion_style());
    files_spinner.finish_with_message("Input files loaded successfully");

    // Output Paths
    let output = current_dir.join(".forge").join(now);
    
    let output_spinner = multi_progress.add(ProgressBar::new_spinner());
    output_spinner.set_style(create_spinner_style());
    output_spinner.set_prefix("Creating");
    output_spinner.enable_steady_tick(Duration::from_millis(80));
    output_spinner.set_message("Preparing output directory...");
    
    tokio::fs::create_dir_all(output.clone()).await?;
    
    output_spinner.set_prefix(success_prefix);
    output_spinner.set_style(create_completion_style());
    output_spinner.finish_with_message(format!("Output directory ready at {}", output.display()));

    // Analyze specification
    let analyze_spinner = multi_progress.add(ProgressBar::new_spinner());
    analyze_spinner.set_style(create_spinner_style());
    analyze_spinner.set_prefix("Analyzing");
    analyze_spinner.enable_steady_tick(Duration::from_millis(80));
    analyze_spinner.set_message("Processing product requirement specifications...");

    let raw_fr = api
        .run(
            workflow,
            Event::new("analyze-spec", product_requirements.clone()),
        )
        .await?;

    let requirements = raw_fr.extract_tag("requirement");
    let requirements_count = requirements.len();
    
    analyze_spinner.set_prefix(success_prefix);
    analyze_spinner.set_style(create_completion_style());
    analyze_spinner.finish_with_message(format!("Discovered {} functional requirements", requirements_count));

    tokio::fs::write(
        output.join("functional-requirements.md"),
        requirements.join("\n\n"),
    )
    .await?;

    // Generate laws from requirements
    let laws_main_spinner = multi_progress.add(ProgressBar::new_spinner());
    laws_main_spinner.set_style(create_spinner_style());
    laws_main_spinner.set_prefix("Generating");
    laws_main_spinner.enable_steady_tick(Duration::from_millis(80));
    laws_main_spinner.set_message(format!("Processing 0/{} requirements...", requirements_count));
    
    // Create a counter for completed requirements
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
            laws_main_spinner.set_message(format!("Completed {}/{} requirements", completed, requirements_count));
            
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
    
    laws_main_spinner.set_prefix(success_prefix);
    laws_main_spinner.set_style(create_completion_style());
    laws_main_spinner.finish_with_message(format!("All {} requirements processed, generated {} laws", requirements_count, laws.len()));

    // Verify pull request against laws
    // Main progress indicator for verification
    let verify_main_spinner = multi_progress.add(ProgressBar::new_spinner());
    verify_main_spinner.set_style(create_spinner_style());
    verify_main_spinner.set_prefix("Verifying");
    verify_main_spinner.enable_steady_tick(Duration::from_millis(80));
    verify_main_spinner.set_message(format!("Completed 0/{} laws...", laws.len()));
    
    // Each law completion will update the spinner message
    let laws_count = laws.len();
    
    // Create a counter for completed laws
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
    
    verify_main_spinner.set_prefix(success_prefix);
    verify_main_spinner.set_style(create_completion_style());
    verify_main_spinner.finish_with_message(format!("All {} laws verified against pull request", laws_count));

    // Save verification results
    let report_spinner = multi_progress.add(ProgressBar::new_spinner());
    report_spinner.set_style(create_spinner_style());
    report_spinner.set_prefix("Reporting");
    report_spinner.enable_steady_tick(Duration::from_millis(80));
    report_spinner.set_message(format!("Creating verification report for {} laws...", verification.len()));
    
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
    
    report_spinner.set_prefix(success_prefix);
    report_spinner.set_style(create_completion_style());
    report_spinner.finish_with_message(format!("Verification report with {} laws completed", verification.len()));

    // Generate summary
    let summary_spinner = multi_progress.add(ProgressBar::new_spinner());
    summary_spinner.set_style(create_spinner_style());
    summary_spinner.set_prefix("Summarizing");
    summary_spinner.enable_steady_tick(Duration::from_millis(80));
    summary_spinner.set_message("Creating summary from verification results...");
    
    let value = json!({
        "pull_request_diff": pull_request,
        "verification_status": verification
    });

    let raw_summary = api
        .run(workflow, Event::new("summarize-reports", value))
        .await?;

    let summary = raw_summary.extract_tag("summary");

    tokio::fs::write(output.join("summary.md"), summary.join("\n")).await?;
    
    summary_spinner.set_prefix(success_prefix);
    summary_spinner.set_style(create_completion_style());
    summary_spinner.finish_with_message(format!("Summary of {} verifications completed", verification.len()));
    
    // Final message - With more styling
    println!("\n\n{:=^80}", " Code Review Complete ");
    println!("\n📊 Reports saved to: {}\n", output.display());
    println!("{:-^80}\n", " Generated Files ");
    println!("  📄 functional-requirements.md - {} requirements", requirements_count);
    println!("  📄 verification.md - {} law verifications", verification.len());
    println!("  📄 summary.md - Final assessment");
    println!("\n{:=^80}\n", "");

    Ok(())
}
