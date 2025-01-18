use serde::de::DeserializeOwned;

#[async_trait::async_trait]
pub trait ToolCallService {
    type Input: DeserializeOwned;
    type Output: serde::Serialize;

    async fn call(&self, input: Self::Input) -> Result<Self::Output, String>;
}
