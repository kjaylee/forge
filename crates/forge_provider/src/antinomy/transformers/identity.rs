use super::Transformer;
use crate::antinomy::request::AntinomyRequest;

/// A transformer that returns the request unchanged
#[derive(Default)]
pub struct Identity;

impl Transformer for Identity {
    fn transform(&self, request: AntinomyRequest) -> AntinomyRequest {
        request
    }
}
