use serde::de::DeserializeOwned;
use serde::Serialize;

use crate::{PermissionRequest, ToolPermissions};

#[async_trait::async_trait]
pub trait ToolCallService: ToolPermissions {
    type Input: DeserializeOwned;
    type Output: Serialize;

    async fn call(&self, input: Self::Input) -> Result<Self::Output, String>;

    async fn permission_check(&self, _input: Self::Input) -> PermissionRequest;
}
