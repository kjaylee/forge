#[derive(Clone, Default, derive_setters::Setters)]
#[setters(strip_option)]
pub struct Workspace {
    pub current_branch: Option<String>,
    pub current_dir: Option<String>,
}
