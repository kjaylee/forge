use anyhow::Result;

/// Struct for handling GitHub PR level comments
pub struct GithubPRCommentator {
    comment: String,
}

impl GithubPRCommentator {
    /// Creates a new instance with the provided PR comment
    pub fn new(comment: String) -> Self {
        Self { comment }
    }

    /// Posts a comment to the GitHub PR
    pub async fn comment(&self) -> Result<()> {
        todo!()
    }
}
