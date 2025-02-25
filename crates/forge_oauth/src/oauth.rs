//! A library for handling OAuth2 authentication with Clerk using OpenID Connect.
//!
//! This crate provides functionality to authenticate users via Clerk's OAuth2 implementation
//! with PKCE (Proof Key for Code Exchange) for enhanced security using the OpenID Connect standard.

use crate::callback::CallbackServer;
use crate::error::AuthError;
use crate::user_info::{UserInfo, UserInfoClient};
use anyhow::Result;
use openidconnect::{
    core::{CoreClient, CoreResponseType},
    AuthUrl, AuthenticationFlow, ClientId, CsrfToken, IssuerUrl, Nonce, OAuth2TokenResponse,
    PkceCodeChallenge, PkceCodeVerifier, RedirectUrl, Scope, TokenUrl,
};

/// Configuration for the OpenID Connect client
#[derive(Clone, Debug)]
pub struct ClerkConfig {
    pub client_id: String,
    pub redirect_url: String,
    pub auth_url: String,
    pub token_url: String,
    pub user_info_url: String,
    pub issuer_url: String,
    pub scope: String,
}

impl Default for ClerkConfig {
    fn default() -> Self {
        Self {
            client_id: "9gKakVrZfk7T1hen".to_string(),
            redirect_url: "http://localhost:8080/callback".to_string(),
            auth_url: "https://legible-finch-79.clerk.accounts.dev/oauth/authorize".to_string(),
            token_url: "https://legible-finch-79.clerk.accounts.dev/oauth/token".to_string(),
            user_info_url: "https://legible-finch-79.clerk.accounts.dev/oauth/userinfo".to_string(),
            issuer_url: "https://legible-finch-79.clerk.accounts.dev".to_string(),
            scope: "email".to_string(),
        }
    }
}

/// The main authentication client
#[derive(Clone)]
pub struct ClerkAuthClient {
    config: ClerkConfig,
    client: CoreClient,
    user_info_client: UserInfoClient,
}

impl ClerkAuthClient {
    /// Create a new client with the given configuration
    pub fn new(config: ClerkConfig) -> Result<Self> {
        // Set up the OpenID Connect client
        let client_id = ClientId::new(config.client_id.clone());
        let redirect_url = RedirectUrl::new(config.redirect_url.clone())
            .map_err(|e| AuthError::ConfigError(format!("Invalid redirect URL: {}", e)))?;

        // We'll create a client manually since we don't have full OpenID discovery
        let issuer_url = IssuerUrl::new(config.issuer_url.clone())
            .map_err(|e| AuthError::ConfigError(format!("Invalid issuer URL: {}", e)))?;

        let auth_url = AuthUrl::new(config.auth_url.clone())
            .map_err(|e| AuthError::ConfigError(format!("Invalid auth URL: {}", e)))?;
        let token_url = TokenUrl::new(config.token_url.clone())
            .map_err(|e| AuthError::ConfigError(format!("Invalid token URL: {}", e)))?;

        // Create the client
        let client = CoreClient::new(
            client_id,
            None, // No client secret for PKCE flow
            issuer_url,
            auth_url,
            Some(token_url),
            None,               // No user info endpoint
            Default::default(), // Default JWKS
        )
        .set_redirect_uri(redirect_url);

        let user_info_client = UserInfoClient::new(config.user_info_url.clone());

        Ok(Self { config, client, user_info_client })
    }

    /// Generate the authorization URL that the user needs to visit
    pub fn generate_auth_url(&self) -> (String, PkceCodeVerifier, CsrfToken, Nonce) {
        // Generate PKCE code verifier and challenge
        let (pkce_challenge, pkce_verifier) = PkceCodeChallenge::new_random_sha256();

        // Generate a CSRF token and nonce
        let csrf_token = CsrfToken::new_random();
        let nonce = Nonce::new_random();

        let csrf_token_clone = csrf_token.clone();
        let nonce_clone = nonce.clone();

        // Generate the authorization URL
        let (auth_url, _, _) = self
            .client
            .authorize_url(
                AuthenticationFlow::<CoreResponseType>::AuthorizationCode,
                move || csrf_token_clone.clone(),
                move || nonce_clone.clone(),
            )
            .add_scope(Scope::new(self.config.scope.clone()))
            .set_pkce_challenge(pkce_challenge)
            .url();

        let auth_url = auth_url.to_string();

        (auth_url, pkce_verifier, csrf_token, nonce)
    }

    /// Complete the OAuth2 flow and return the token and user info
    pub async fn complete_auth_flow(
        &self,
    ) -> Result<(openidconnect::core::CoreTokenResponse, UserInfo)> {
        // 1. Generate authorization URL with PKCE
        let (auth_url, pkce_verifier, csrf_token, _nonce) = self.generate_auth_url();

        // 2. Open browser for user authentication
        println!("Opening browser for authentication...");
        println!("If the browser doesn't open automatically, please visit this URL:");
        println!("{}", auth_url);

        if let Err(e) = open::that(&auth_url) {
            println!("Failed to open browser automatically: {}", e);
            println!("Please open the URL manually in your browser.");
        }

        // 3. Start the callback server and wait for the response
        println!("Waiting for authentication response...");
        let callback_result = CallbackServer::default()
            .wait_for_callback(120)
            .await
            .map_err(AuthError::from)?;

        // 4. Verify the state to prevent CSRF attacks
        if callback_result.state != *csrf_token.secret() {
            return Err(AuthError::StateMismatch.into());
        }

        // 5. Exchange the code for a token
        let token_response = self.exchange_code_for_token(callback_result.code, pkce_verifier).await?;

        // 6. Get user information
        let user_info = self.user_info_client.get_user_info(token_response.access_token()).await?;

        Ok((token_response, user_info))
    }

    /// Exchange the authorization code for an access token
    async fn exchange_code_for_token(
        &self,
        code: String,
        pkce_verifier: PkceCodeVerifier,
    ) -> Result<openidconnect::core::CoreTokenResponse> {
        println!("Exchanging code for token...");

        // Clone the client before moving it into the spawn_blocking task
        let client = self.client.clone();
        
        // Use a blocking task since the openidconnect library uses blocking requests
        tokio::task::spawn_blocking(move || {
            client
                .exchange_code(openidconnect::AuthorizationCode::new(code))
                .set_pkce_verifier(pkce_verifier)
                .request(openidconnect::reqwest::http_client)
                .map_err(|e| AuthError::TokenExchangeError(e.to_string()).into())
        })
        .await?
    }
}
