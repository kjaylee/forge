use crate::Permission;

/// Trait for defining required permissions for a tool
pub trait ToolPermissions {
    /// Get required permissions for this tool
    fn required_permissions(&self) -> Vec<Permission> {
        Vec::new()
    }
}
