use serde::Serialize;

#[derive(Serialize)]
pub struct PullRequest;

impl Default for PullRequest {
    fn default() -> Self {
        Self::new()
    }
}

impl PullRequest {
    pub fn new() -> Self {
        Self
    }

    pub fn modified_files(&self) -> Vec<String> {
        todo!()
    }
}

#[derive(Serialize, Clone)]
pub struct Rule {
    pub content: String,
    pub importance: Importance,
}

#[derive(Serialize, Clone)]
pub enum Importance {
    High,
    Medium,
    Low,
}

pub struct RuleList {
    pub rules: Vec<Rule>,
}
