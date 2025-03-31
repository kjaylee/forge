use std::sync::Arc;

use forge_api::API;

use super::command::ForgeCommandService;
use crate::domain::ForgeServices;

pub struct StandardForgeServices<A: API> {
    api: Arc<A>,
    command_service: Arc<ForgeCommandService>,
}

impl<A: API> StandardForgeServices<A> {
    pub fn new(api: Arc<A>) -> Self {
        Self {
            api,
            command_service: Arc::new(ForgeCommandService::default()),
        }
    }
}

impl<A: API + 'static> ForgeServices for StandardForgeServices<A> {
    type API = A;
    type CommandService = ForgeCommandService;

    fn api(&self) -> &Self::API {
        &self.api
    }

    fn command_service(&self) -> &Self::CommandService {
        &self.command_service
    }
}
