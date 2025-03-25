use std::{path::Path, sync::Arc, time::Duration};
use std::fs;

use anyhow::Result;
use forge_api::{Event, ForgeAPI, API};
use forge_review::{Task, TaskError, TaskErrorKind};
use forge_services::ForgeServices;
use forge_infra::ForgeInfra;
use forge_domain::Workflow;

type ForgeAPIType = ForgeAPI<ForgeServices<ForgeInfra>>;

fn create_spec_task(api: Arc<ForgeAPIType>, workflow: Workflow, spec: String) -> Task<()> {
    Task::action(
        move || {
            let api = Arc::clone(&api);
            let workflow = workflow.clone();
            let spec = spec.clone();
            async move {
                let event = Event::new("generate_law", &spec);
                let _ = api.run(&workflow, event).await;
                Ok(())
            }
        },
        1,
        Duration::from_millis(10),
    )
}

#[tokio::main]
async fn main() -> Result<()> {
    let api = Arc::new(ForgeAPI::init(false));
    let path = Path::new("./review.yaml");
    let workflow = api.load(Some(path)).await?;

    // First task: analyze the spec to generate functional requirements
    let workflow_clone = workflow.clone();
    let api_clone = Arc::clone(&api);
    let analyze_task = Task::action(
        move || {
            let api = Arc::clone(&api_clone);
            let workflow = workflow_clone.clone();
            async move {
                let event = Event::new("analyze-spec", "@./todo-mark-done-prd.md");
                let _ = api.run(&workflow, event).await;
                Ok(())
            }
        },
        1,
        Duration::from_millis(10),
    );

    // Second task: process the generated functional requirements in parallel
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
                
                let specifications: Vec<String> = content
                    .split("##")
                    .filter(|s| !s.trim().is_empty())
                    .map(|s| s.trim().to_string())
                    .collect();

                // Create parallel tasks for each specification
                let tasks = specifications
                    .into_iter()
                    .map(|spec| create_spec_task(Arc::clone(&api), workflow.clone(), spec))
                    .collect();

                // Execute all tasks in parallel
                let parallel_task = Task::parallel(tasks);
                parallel_task.execute().await?;
                Ok(())
            }
        },
        1,
        Duration::from_millis(10),
    );

    // Chain the tasks together: first analyze, then process requirements
    let workflow = analyze_task.chain(process_requirements_task);
    
    // Execute the complete workflow
    workflow.execute().await?;

    Ok(())
}
