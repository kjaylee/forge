use forge_domain::{Permission, ToolPermissions};

impl ToolPermissions for super::FSRead {
    fn required_permissions(&self) -> Vec<Permission> {
        vec![Permission::Read]
    }
}

impl ToolPermissions for super::FSWrite {
    fn required_permissions(&self) -> Vec<Permission> {
        vec![Permission::Write]
    }
}

impl ToolPermissions for super::FSList {
    fn required_permissions(&self) -> Vec<Permission> {
        vec![Permission::Read]
    }
}

impl ToolPermissions for super::FSSearch {
    fn required_permissions(&self) -> Vec<Permission> {
        vec![Permission::Read]
    }
}

impl ToolPermissions for super::FSFileInfo {
    fn required_permissions(&self) -> Vec<Permission> {
        vec![Permission::Read]
    }
}

impl ToolPermissions for super::FSReplace {
    fn required_permissions(&self) -> Vec<Permission> {
        vec![Permission::Read, Permission::Write]
    }
}