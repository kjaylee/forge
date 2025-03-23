use serde::Serialize;

/// Sample Response available at:
/// PR https://api.github.com/repos/antinomyhq/forge/pulls/200
/// DIFF https://patch-diff.githubusercontent.com/raw/antinomyhq/forge/pull/200.diff
#[derive(Serialize)]
pub struct PullRequest {
    id: u64,
    files: Vec<File>,
}

/// Sample Response available at: 
/// https://api.github.com/repos/antinomyhq/forge/pulls/200/files
#[derive(Serialize)]
pub struct File {
    sha: String,
    filename: String,
    patch: String,
}

impl PullRequest {
    pub fn modified_files(&self) -> Vec<String> {
        self.files.iter().map(|f| f.filename.clone()).collect()
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
