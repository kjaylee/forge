use forge_oauth::*;

#[tokio::main]
async fn main() {
    // Create configuration
    let config = ClerkConfig::default();
    let client = ClerkAuthClient::new(config).unwrap();

    // Start OAuth flow - this will open your browser
    match client.complete_auth_flow().await {
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
