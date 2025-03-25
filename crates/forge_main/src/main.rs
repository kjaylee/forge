use std::fs;
use std::{path::Path, sync::Arc, time::Duration};

use anyhow::Result;
use forge_api::{Event, ForgeAPI, API};
use forge_domain::{FunctionalRequirements, Workflow};
use forge_infra::ForgeInfra;
use forge_review::{Task, TaskError, TaskErrorKind};
use forge_services::ForgeServices;

type ForgeAPIType = ForgeAPI<ForgeServices<ForgeInfra>>;

const ARTIFACTS_DIR: &str = "./prd-verification-workflow-artifacts";
const LAWS_DIR: &str = "./prd-verification-workflow-artifacts/laws";
const VERIFICATION_DIR: &str = "./prd-verification-workflow-artifacts/verification";

fn create_law_generation_task(
    api: Arc<ForgeAPIType>,
    workflow: Workflow,
    event: String,
) -> Task<()> {
    Task::action(
        move || {
            let api = Arc::clone(&api);
            let workflow = workflow.clone();
            let req = event.clone();
            async move {
                let event = Event::new("generate-laws", req);
                api.run(&workflow, event)
                    .await
                    .map_err(|e| TaskError::new(TaskErrorKind::ActionFailed, e.to_string()))?;
                Ok(())
            }
        },
        1,
        Duration::from_millis(10),
    )
}

fn create_verification_task(api: Arc<ForgeAPIType>, workflow: Workflow, event: String) -> Task<()> {
    Task::action(
        move || {
            let api = Arc::clone(&api);
            let workflow = workflow.clone();
            let req_id = event.clone();
            async move {
                let verify_event = Event::new("verify-pr", &req_id);
                api.run(&workflow, verify_event)
                    .await
                    .map_err(|e| TaskError::new(TaskErrorKind::ActionFailed, e.to_string()))?;
                Ok(())
            }
        },
        1,
        Duration::from_millis(10),
    )
}

fn setup_directories() -> Result<()> {
    for dir in [ARTIFACTS_DIR, LAWS_DIR, VERIFICATION_DIR] {
        fs::create_dir_all(dir)?;
    }
    Ok(())
}

#[tokio::main]
async fn main() -> Result<()> {
    // Initialize API and load workflow configuration
    let api = Arc::new(ForgeAPI::init(false));
    let path = Path::new("./review.yaml");
    let workflow = api.load(Some(path)).await?;

    let artifact_path = Path::new("./prd-verification-workflow-artifacts");

    // Create necessary directories
    setup_directories()?;

    // 1. Organizer Task: Analyze spec and generate functional requirements
    let workflow_clone = workflow.clone();
    let api_clone = Arc::clone(&api);
    let analyze_task = Task::action(
        move || {
            let api = Arc::clone(&api_clone);
            let workflow = workflow_clone.clone();
            async move {
                let raw_event = serde_json::json!({
                    "specification_path": "@./todo-mark-done-prd.md",
                    "output_path": artifact_path.join("functional_req.md"),
                });
                let event = Event::new("analyze-spec", raw_event);
                api.run(&workflow, event)
                    .await
                    .map_err(|e| TaskError::new(TaskErrorKind::ActionFailed, e.to_string()))?;
                Ok(())
            }
        },
        1,
        Duration::from_millis(10),
    );

    // 2. Process requirements in parallel, where each requirement has its own sequence of:
    //    a. Generate TLA+ spec
    let workflow_clone = workflow.clone();
    let api_clone = Arc::clone(&api);
    let tla_task = Task::action(
        move || {
            let api = Arc::clone(&api_clone);
            let workflow = workflow_clone.clone();
            async move {
                // Read and parse functional requirements
                let content = fs::read_to_string(artifact_path.join("functional_req.md"))
                    .map_err(|e| TaskError::new(TaskErrorKind::ActionFailed, e.to_string()))?;

                let functional_reqs = FunctionalRequirements::parse(&content)
                    .map_err(|e| TaskError::new(TaskErrorKind::ActionFailed, e.to_string()))?;

                // Create parallel sequences for each requirement
                let tasks = functional_reqs
                    .requirements
                    .into_iter()
                    .map(|req| create_law_generation_task(Arc::clone(&api), workflow.clone(), serde_json::json!({
                        "functional_requirement": req,
                        "output_path": artifact_path.join("laws").join(req.id.clone() + ".tla"),
                    }).to_string()))
                    .collect();

                // Execute all requirement processing sequences in parallel
                let parallel_task = Task::parallel(tasks);
                parallel_task.execute().await?;
                Ok(())
            }
        },
        1,
        Duration::from_millis(10),
    );

    // 3. Verification Task: Verify PRs
    let workflow_clone = workflow.clone();
    let api_clone = Arc::clone(&api);
    let verification_task = Task::action(
        move || {
            let api = Arc::clone(&api_clone);
            let workflow = workflow_clone.clone();
            async move {
                // Execute all requirement processing sequences in parallel
                let laws_dir = artifact_path.join("laws");
                let entries = fs::read_dir(&laws_dir)
                    .map_err(|e| TaskError::new(TaskErrorKind::ActionFailed, e.to_string()))?;

                // Create verification tasks for each law file
                let verification_tasks: Vec<Task<()>> = entries
                    .filter_map(|entry| entry.ok())
                    .filter(|entry| entry.path().is_file())
                    .filter_map(|entry| {
                        let file_content = match fs::read_to_string(entry.path()) {
                            Ok(content) => content,
                            Err(e) => {
                                eprintln!("Failed to read file {:?}: {}", entry.path(), e);
                                return None;
                            }
                        };
                        Some(create_verification_task(
                            Arc::clone(&api),
                            workflow.clone(),
                            serde_json::json!({
                                "verification_content": file_content,
                                "pull_request_path": artifact_path.join("pull-request.diff"),
                                "output_path": artifact_path.join("verification").join(entry.file_name()),
                            }).to_string(),
                        ))
                    })
                    .collect();

                // Execute all verification tasks in parallel
                let parallel_verification = Task::parallel(verification_tasks);
                parallel_verification.execute().await?;

                Ok(())
            }
        },
        1,
        Duration::from_millis(10),
    );

    // 4. Summarizer Task: Generate final report
    let workflow_clone = workflow.clone();
    let api_clone = Arc::clone(&api);
    let summary_task = Task::action(
        move || {
            let api = Arc::clone(&api_clone);
            let workflow = workflow_clone.clone();
            async move {
                let raw_event = serde_json::json!({
                    "verification_path": artifact_path.join(VERIFICATION_DIR).to_string_lossy(),
                    "output_path": artifact_path.join("final_report.md"),
                    "pull_request_path": artifact_path.join("pull-request.diff"),
                });
                let event = Event::new(
                    "summarize-reports",
                    raw_event.to_string()
                );
                api.run(&workflow, event)
                    .await
                    .map_err(|e| TaskError::new(TaskErrorKind::ActionFailed, e.to_string()))?;
                Ok(())
            }
        },
        1,
        Duration::from_millis(10),
    );

    // Chain the main workflow steps
    let complete_workflow = analyze_task
        .chain(tla_task)
        .chain(verification_task)
        .chain(summary_task);

    // Execute the complete workflow
    complete_workflow.execute().await?;

    Ok(())
}
