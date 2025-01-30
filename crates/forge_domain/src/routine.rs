use crate::{Agent, ForgeDomain};

pub struct Routine<'a, S, U, D: ForgeDomain> {
    system: S,
    user: U,
    domain: &'a D,
}

impl<'a, S, U, D: ForgeDomain> Routine<'a, S, U, D> {
    pub fn new(domain: &'a D, system: S, user: U) -> Self {
        Self { system, user, domain }
    }

    pub fn launch(&self, agent: Agent<S, U>) -> anyhow::Result<()> {
        todo!()
    }
}
