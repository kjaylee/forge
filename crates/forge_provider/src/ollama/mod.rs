pub mod error;
pub mod model;
pub mod provider;
pub mod request;
pub mod response;

use provider::{Config, Ollama};

use crate::{ProviderService, Service};

impl Service {
    pub fn ollama() -> impl ProviderService {
        Ollama::new(Config::default())
    }
}
