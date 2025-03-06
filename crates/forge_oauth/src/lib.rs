mod callback;
mod error;
mod oauth;
mod user_info;

pub use error::AuthError;
pub use oauth::*;
pub use user_info::UserInfo;

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    #[ignore] // This test is ignored as it requires manual intervention
    async fn demo_oauth_flow() {
        // Create configuration
        let config = ClerkConfig::default();
        let client = ClerkAuthClient::new(config).unwrap();
        let auth_flow_state = client.generate_auth_url();
        // Start OAuth flow - this will open your browser
        let result = client.complete_auth_flow(auth_flow_state).await;

        if let Err(e) = result {
            println!("Error during authentication: {}", e);
            panic!("Authentication failed");
        } else {
            println!("Successfully authenticated!");
        }
    }
}
