use anyhow::Result;
use std::path::PathBuf;

/// Struct for handling GitHub PR file comments
pub struct GithubFileCommentator {
    file_feedback: Vec<(PathBuf, String)>,
}

impl GithubFileCommentator {
    /// Creates a new instance with the provided file feedback
    pub fn new(file_feedback: Vec<(PathBuf, String)>) -> Self {
        Self { file_feedback }
    }

    /// Posts comments to GitHub for each file
    pub async fn comment(&self) -> Result<()> {
        todo!()
    }
}
