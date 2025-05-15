use super::Transformer;
use crate::antinomy::request::OpenRouterRequest;

/// A transformer that returns the request unchanged
#[derive(Default)]
pub struct Identity;

impl Transformer for Identity {
    fn transform(&self, request: OpenRouterRequest) -> OpenRouterRequest {
        request
    }
}
