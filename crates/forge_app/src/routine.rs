use forge_domain::Agent;

use crate::ForgeAPI;

pub struct Routine<'a, S, U, API> {
    system: S,
    user: U,
    api: &'a API,
}

pub struct Exit;

impl<'a, S, U, API: ForgeAPI> Routine<'a, S, U, API> {
    pub fn new(app: &'a API, system: S, user: U) -> Self {
        Self { system, user, api: app }
    }

    pub async fn launch(&self, agent: Agent<S, U>) -> anyhow::Result<Exit> {
        todo!()
    }
}
