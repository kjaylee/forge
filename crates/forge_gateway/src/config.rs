use serde::Deserialize;

/// Configuration for the application
#[derive(Debug, Deserialize)]
pub struct Config {
    /// Provider API key
    pub provider_key: String,
    /// Provider Url
    pub provider_url: String,
    /// Supabase URL
    pub supabase_url: String,
    /// Supabase API key
    pub supabase_key: String,
    /// Clerk secret key for authentication
    pub clerk_secret_key: String,
    /// Server host
    pub host: String,
    /// Server port
    pub port: u16,
    /// Api key prefix
    pub api_key_prefix: String,
    /// APi key length
    pub api_key_length: u16,
}

impl Config {
    pub fn from_env() -> Self {
        let provider = forge_domain::Provider::from_env().expect("Failed to load provider");
        let provider_url = provider.to_base_url().to_string();
        let provider_key = provider.get_key();

        Self {
            provider_key,
            provider_url,
            supabase_url: std::env::var("SUPABASE_URL").expect("SUPABASE_URL is required"),
            supabase_key: std::env::var("SUPABASE_KEY").expect("SUPABASE_KEY is required"),
            clerk_secret_key: std::env::var("CLERK_SECRET_KEY")
                .expect("CLERK_SECRET_KEY is required"),
            host: std::env::var("HOST").expect("HOST is required"),
            port: std::env::var("PORT")
                .expect("PORT is required")
                .parse()
                .expect("PORT must be a number"),
            api_key_length: std::env::var("API_KEY_LENGTH")
                .expect("API_KEY_LENGTH is required")
                .parse()
                .expect("API_KEY_LENGTH must be a number"),
            api_key_prefix: std::env::var("API_KEY_PREFIX").expect("API_KEY_PREFIX is required"),
        }
    }

    /// Returns the server address
    pub fn server_addr(&self) -> String {
        format!("{}:{}", self.host, self.port)
    }
}
