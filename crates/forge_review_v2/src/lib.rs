use std::fmt::{Debug, Display};
use std::marker::PhantomData;

use async_trait::async_trait;

// Core error type
#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("Analysis Agent error: {0}")]
    Analysis(String),
    #[error("Law Generation Agent error: {0}")]
    Generation(String),
    #[error("Verification Agent error: {0}")]
    Verification(String),
    #[error("Summarization Agent error: {0}")]
    Summarization(String),
}

// Core workflow trait
#[async_trait]
pub trait WorkflowStep {
    type Input: Clone + Send + Sync;
    type Output: Send;
    type Error: Display + Send;

    async fn execute(&self, input: Self::Input) -> Result<Self::Output, Self::Error>;
}

// Composition trait
pub trait StepCompose: Sized {
    fn pipe<Next>(self, next: Next) -> Sequence<Self, Next>
    where
        Self: WorkflowStep,
        Next: WorkflowStep<Input = Self::Output>,
    {
        Sequence(self, next)
    }
}

// Implement composition for all workflow steps
impl<T: WorkflowStep> StepCompose for T {}

// State markers
#[derive(Clone, Debug)]
pub struct Initial;
#[derive(Clone, Debug)]
pub struct Analyzed;
#[derive(Clone, Debug)]
pub struct Generated;
#[derive(Clone, Debug)]
pub struct Verified;

#[derive(Clone, Debug)]
pub struct Finished;

// State wrapper
#[derive(Clone, Debug)]
pub struct WorkflowState<S: Clone, T: Clone + Debug>(pub T, pub PhantomData<S>);

impl<T: Clone + Debug> WorkflowState<Initial, T> {
    pub fn new(input: T) -> Self {
        Self(input, PhantomData)
    }
}

// Composition structures
pub struct Sequence<A, B>(pub A, pub B);

#[async_trait]
impl<A, B> WorkflowStep for Sequence<A, B>
where
    A: WorkflowStep + Send + Sync,
    B: WorkflowStep<Input = A::Output> + Send + Sync,
    A::Output: Send,
{
    type Input = A::Input;
    type Output = B::Output;
    type Error = Error;

    async fn execute(&self, input: Self::Input) -> Result<Self::Output, Self::Error> {
        let intermediate = self
            .0
            .execute(input)
            .await
            .map_err(|e| Error::Analysis(e.to_string()))?;
        self.1
            .execute(intermediate)
            .await
            .map_err(|e| Error::Generation(e.to_string()))
    }
}

// Concrete steps module
mod functional_req;
pub mod steps;

// Re-exports
pub mod prelude {
    pub use super::functional_req::FunctionalRequirements;
    pub use super::steps::{
        AnalyzeSpec, GenerateLaws, Law, Requirements, SpecDocument, VerifyLaws,
    };
    pub use super::{
        Analyzed, Error, Generated, Initial, StepCompose, Verified, WorkflowState, WorkflowStep,
    };
}

pub fn extract_tag_content<'a>(text: &'a str, tag_name: &str) -> Vec<&'a str> {
    let opening_tag = format!("<{}>", tag_name);
    let closing_tag = format!("</{}>", tag_name);
    let mut results = Vec::new();
    let mut current_position = 0;
    
    while let Some(start_idx) = text[current_position..].find(&opening_tag) {
        // Adjust start_idx to account for the current position offset
        let absolute_start_idx = current_position + start_idx;
        // Find the next closing tag after this opening tag
        if let Some(end_idx) = text[absolute_start_idx..].find(&closing_tag) {
            // Adjust end_idx to account for the absolute_start_idx offset
            let absolute_end_idx = absolute_start_idx + end_idx;
            let content_start = absolute_start_idx + opening_tag.len();
            
            if content_start < absolute_end_idx {
                // Extract and trim the content between the tags
                results.push(text[content_start..absolute_end_idx].trim());
            }
            
            // Move past this closing tag for the next iteration
            current_position = absolute_end_idx + closing_tag.len();
        } else {
            // No matching closing tag found, exit the loop
            break;
        }
    }
    
    results
}

pub trait XMLExtensions {
    fn extract_tag(&self, tag: &str) -> Vec<&str>;
}

impl<T: AsRef<str>> XMLExtensions for T {
    fn extract_tag(&self, tag: &str) -> Vec<&str> {
        extract_tag_content(self.as_ref(), tag)
    }
}
