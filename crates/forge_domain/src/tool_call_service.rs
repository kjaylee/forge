use serde::de::DeserializeOwned;
use serde::Serialize;

use crate::PermissionRequest;

#[async_trait::async_trait]
pub trait ToolCallService {
    type Input: DeserializeOwned;
    type Output: Serialize;

    async fn call(&self, input: Self::Input) -> Result<Self::Output, String>;

    fn permission_check(&self, _input: Self::Input) -> PermissionRequest;
}
