use std::{path::Path, sync::Arc, time::Duration};
use std::fs;

use anyhow::Result;
use forge_api::{Event, ForgeAPI, API};
use forge_review::{Task, TaskError, TaskErrorKind};
use forge_services::ForgeServices;
use forge_infra::ForgeInfra;
use forge_domain::{Workflow, FunctionalRequirements, Requirement};

type ForgeAPIType = ForgeAPI<ForgeServices<ForgeInfra>>;

const ARTIFACTS_DIR: &str = "./prd-verification-workflow-artifacts";
const LAWS_DIR: &str = "./prd-verification-workflow-artifacts/laws";
const VERIFICATION_DIR: &str = "./prd-verification-workflow-artifacts/verification";

fn create_law_generation_task(api: Arc<ForgeAPIType>, workflow: Workflow, req: Requirement) -> Task<()> {
    Task::action(
        move || {
            let api = Arc::clone(&api);
            let workflow = workflow.clone();
            let req = req.clone();
            async move {
                let event = Event::new("generate-laws", req.to_string());
                api.run(&workflow, event).await
                    .map_err(|e| TaskError::new(TaskErrorKind::ActionFailed, e.to_string()))?;
                Ok(())
            }
        },
        1,
        Duration::from_millis(10),
    )
}

fn create_verification_task(api: Arc<ForgeAPIType>, workflow: Workflow, req_id: String) -> Task<()> {
    Task::action(
        move || {
            let api = Arc::clone(&api);
            let workflow = workflow.clone();
            let req_id = req_id.clone();
            async move {
                let verify_event = Event::new("verify-pr", &req_id);
                api.run(&workflow, verify_event).await
                    .map_err(|e| TaskError::new(TaskErrorKind::ActionFailed, e.to_string()))?;
                Ok(())
            }
        },
        1,
        Duration::from_millis(10),
    )
}

fn create_requirement_processing_sequence(
    api: Arc<ForgeAPIType>,
    workflow: Workflow,
    req: Requirement,
) -> Task<()> {
    // Create a sequence for each requirement:
    // 1. Generate TLA+ spec
    // 2. Verify the generated spec
    let api_clone = Arc::clone(&api);
    let workflow_clone = workflow.clone();
    let req_id = req.id.clone();
    
    // Create individual tasks
    let gen_task = create_law_generation_task(api, workflow, req);
    let verify_task = create_verification_task(api_clone, workflow_clone, req_id);
    
    // Combine them in sequence
    Task::sequence(vec![gen_task, verify_task])
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
                let event = Event::new("analyze-spec", "@./todo-mark-done-prd.md");
                api.run(&workflow, event).await
                    .map_err(|e| TaskError::new(TaskErrorKind::ActionFailed, e.to_string()))?;
                Ok(())
            }
        },
        1,
        Duration::from_millis(10),
    );

    // 2. Process requirements in parallel, where each requirement has its own sequence of:
    //    a. Generate TLA+ spec
    //    b. Verify the spec
    let workflow_clone = workflow.clone();
    let api_clone = Arc::clone(&api);
    let process_requirements_task = Task::action(
        move || {
            let api = Arc::clone(&api_clone);
            let workflow = workflow_clone.clone();
            async move {
                // Read and parse functional requirements
                let content = fs::read_to_string("functional_req.md")
                    .map_err(|e| TaskError::new(TaskErrorKind::ActionFailed, e.to_string()))?;
                
                let functional_reqs = FunctionalRequirements::parse(&content)
                    .map_err(|e| TaskError::new(TaskErrorKind::ActionFailed, e.to_string()))?;

                // Create parallel sequences for each requirement
                let tasks = functional_reqs.requirements
                    .into_iter()
                    .map(|req| create_requirement_processing_sequence(Arc::clone(&api), workflow.clone(), req))
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

    // 3. Summarizer Task: Generate final report
    let workflow_clone = workflow.clone();
    let api_clone = Arc::clone(&api);
    let summary_task = Task::action(
        move || {
            let api = Arc::clone(&api_clone);
            let workflow = workflow_clone.clone();
            async move {
                let event = Event::new("summarize-reports", VERIFICATION_DIR);
                api.run(&workflow, event).await
                    .map_err(|e| TaskError::new(TaskErrorKind::ActionFailed, e.to_string()))?;
                Ok(())
            }
        },
        1,
        Duration::from_millis(10),
    );

    // Chain the main workflow steps
    let complete_workflow = analyze_task
        .chain(process_requirements_task)
        .chain(summary_task);
    
    // Execute the complete workflow
    complete_workflow.execute().await?;

    Ok(())
}
