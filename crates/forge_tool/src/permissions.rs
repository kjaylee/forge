use forge_domain::{Permission, ToolPermissions};

use crate::approve::Approve;
use crate::ask::AskFollowUpQuestion;
use crate::outline::Outline;
use crate::select::SelectTool;
use crate::shell::Shell;
use crate::think::Think;

// No permissions needed for Think
impl ToolPermissions for Think {}

// Outline needs read permission
impl ToolPermissions for Outline {
    fn required_permissions(&self) -> Vec<Permission> {
        vec![Permission::Read]
    }
}

// No permissions needed for SelectTool
impl ToolPermissions for SelectTool {}

// No permissions needed for Approve
impl ToolPermissions for Approve {}

impl ToolPermissions for Shell {
    fn required_permissions(&self) -> Vec<Permission> {
        vec![Permission::Execute]
    }
}

impl ToolPermissions for AskFollowUpQuestion {
    fn required_permissions(&self) -> Vec<Permission> {
        vec![]
    }
}
