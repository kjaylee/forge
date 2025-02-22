mod combine;
mod drop_tool_call;
mod identity;
mod open_ai;
mod pipeline;
mod set_cache;
mod tool_choice;
mod when;

use combine::Combine;
pub use pipeline::ProviderPipeline;
use when::When;

use crate::open_router::request::OpenRouterRequest;

/// A trait for transforming OpenRouterRequest based on model-specific
/// requirements
pub trait Transformer {
    /// Transform the request according to the transformer's logic
    fn transform(&self, request: OpenRouterRequest) -> OpenRouterRequest;

    /// Combines this transformer with another, creating a new transformer that
    /// applies both transformations in sequence
    fn combine<Other>(self, other: Other) -> Combine<Self, Other>
    where
        Self: Sized,
    {
        Combine(self, other)
    }

    /// Creates a conditional transformer that only applies the transformation
    /// if the given condition is true
    fn when<F: Fn(&OpenRouterRequest) -> bool>(self, condition: F) -> When<Self, F>
    where
        Self: Sized,
    {
        When(self, condition)
    }

    /// Creates a conditional transformer that only applies the transformation
    /// if the model name matches the given predicate
    fn when_name(
        self,
        model: impl Fn(&str) -> bool,
    ) -> When<Self, impl Fn(&OpenRouterRequest) -> bool>
    where
        Self: Sized,
    {
        self.when(move |r| r.model.as_ref().is_some_and(|m| model(m.as_str())))
    }
}
