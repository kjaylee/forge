use generate::Generate;
use gh_workflow_tailcall::*;

use crate::jobs::{build, draft_release};

/// Generate the main CI workflow
pub fn generate_ci_workflow() {
    let mut workflow = StandardWorkflow::default()
        .auto_fix(true)
        .to_ci_workflow()
        .concurrency(Concurrency {
            group: "${{ github.workflow }}-${{ github.ref }}".to_string(),
            cancel_in_progress: None,
            limit: None,
        })
        .add_env(("OPENROUTER_API_KEY", "${{secrets.OPENROUTER_API_KEY}}"));

    // Get the jobs
    let build_job = workflow.jobs.clone().unwrap().get("build").unwrap().clone();
    let draft_release_job = draft_release::create_draft_release_job();

    // Add jobs to the workflow
    workflow = workflow.add_job("draft_release", draft_release_job.clone());
    workflow = workflow.add_job("build-release-pr", build::create_build_release_pr_job());
    workflow = workflow.add_job(
        "build-release",
        build::create_build_release_main_job(&build_job, &draft_release_job),
    );

    workflow.generate().unwrap();
}

/// Generate homebrew release workflow
pub fn generate_homebrew_workflow() {
    let homebrew_workflow = crate::jobs::homebrew::create_homebrew_workflow();

    Generate::new(homebrew_workflow)
        .name("homebrew-release.yml")
        .generate()
        .unwrap();
}

/// Generate npm release workflow
pub fn generate_npm_workflow() {
    let npm_workflow = crate::jobs::npm::create_npm_workflow();

    Generate::new(npm_workflow)
        .name("npm-release.yml")
        .generate()
        .unwrap();
}

/// Generate release drafter workflow
pub fn generate_release_drafter_workflow() {
    let release_drafter_workflow = crate::jobs::release_drafter::create_release_drafter_workflow();

    Generate::new(release_drafter_workflow)
        .name("release-drafter.yml")
        .generate()
        .unwrap();
}
