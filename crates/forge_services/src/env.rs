use crate::EnvironmentInfra;
use forge_app::EnvironmentService;
use forge_domain::Environment;
use std::sync::Arc;

pub struct ForgeEnvironmentService<F>(Arc<F>);

impl<F> ForgeEnvironmentService<F> {
    pub fn new(infra: Arc<F>) -> Self {
        Self(infra)
    }
}

impl<F: EnvironmentInfra> EnvironmentService for ForgeEnvironmentService<F> {
    fn get_environment(&self) -> Environment {
        self.0.get_environment()
    }
}
