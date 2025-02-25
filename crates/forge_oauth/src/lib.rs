mod oauth;
mod callback;
mod error;
mod user_info;

pub use oauth::*;
pub use error::AuthError;
pub use user_info::UserInfo;

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn demo_oauth_flow() {
        // Create configuration
        let config = ClerkConfig::default();
        let client = ClerkAuthClient::new(config).unwrap();

        // Start OAuth flow - this will open your browser
        match client.complete_auth_flow() {
            Ok((token, user_info)) => {
                println!("Successfully authenticated!");
                println!("User Info: {:?}", user_info);
                println!("Token: {:#?}", token);
            }
            Err(e) => {
                println!("Error during authentication: {}", e);
            }
        }
    }
}
