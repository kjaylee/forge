use crate::Event;

pub mod posthog;

///
/// Defines the interface for an event collector.
#[async_trait::async_trait]
pub trait Collect: Send + Sync {
    async fn collect(&self, event: Event) -> super::Result<()>;
    async fn identify(
        &self,
        distinct_id: String,
        properties: std::collections::HashMap<String, serde_json::Value>,
    ) -> super::Result<()>;
}
