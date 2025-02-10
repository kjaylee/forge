mod env;
mod prompts;
mod repo;
mod schema;
mod service;
mod sqlite;
mod workflow;

pub use env::*;
use forge_domain::ForgeDomain;
pub use service::{APIService, Service};

pub trait ForgeApp: ForgeDomain {}
