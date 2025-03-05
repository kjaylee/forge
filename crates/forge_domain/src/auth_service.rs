use anyhow::Result;

/// Service responsible for authentication operations
#[async_trait::async_trait]
pub trait AuthService: Send + Sync + 'static {
    /// Authenticates the user and stores credentials
    async fn login(&self) -> Result<()>;

    /// Logs out the user by removing stored credentials
    /// Returns true if credentials were found and removed, false otherwise
    fn logout(&self) -> Result<bool>;

    /// Checks if the user is currently authenticated
    fn is_authenticated(&self) -> bool;

    /// Retrieves the current authentication token if available
    /// Returns the token as a string if found, or an error if not authenticated
    fn get_auth_token(&self) -> Option<String>;
}
