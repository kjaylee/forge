use std::sync::Arc;

use axum::serve;
use clerk_rs::{clerk::Clerk, validators::authorizer::ClerkAuthorizer, ClerkConfiguration};
use forge_gateway::{
    config::Config,
    presentation::routes::app,
    service::{ApiKeyService, ProxyService},
    ApiKeyRepositoryImpl, KeyGeneratorServiceImpl,
};
use forge_open_router::ProviderBuilder;
use postgrest::Postgrest;
use tokio::net::TcpListener;
use tower_http::cors::{Any, CorsLayer};
use tracing::info;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Load environment variables
    dotenv::dotenv().ok();

    info!("Starting Forge Gateway V3");
    // Load configuration
    let config = Config::from_env();

    // setup provider
    let provider = ProviderBuilder::from_url(config.provider_url.clone())
        .with_key(config.provider_key.clone())
        .build()
        .expect("Failed to build provider");

    // Initialize Supabase client
    let client = Postgrest::new(&config.supabase_url).insert_header("apikey", &config.supabase_key);

    // Initialize dependencies
    let key_gen_service = Arc::new(KeyGeneratorServiceImpl::new(128, "sk-forge-api01-"));
    let api_key_repository_impl = Arc::new(ApiKeyRepositoryImpl::new(client));
    let api_key_service = Arc::new(ApiKeyService::new(api_key_repository_impl, key_gen_service));
    let proxy_service = Arc::new(ProxyService::new(provider)?);

    // Initialize Clerk auth
    let clerk_config =
        ClerkConfiguration::new(None, None, Some(config.clerk_secret_key.clone()), None);
    let clerk = Arc::new(ClerkAuthorizer::new(Clerk::new(clerk_config), true));

    // Create CORS layer
    let cors = CorsLayer::new()
        .allow_methods(Any)
        .allow_headers(Any)
        .allow_origin(Any);

    // Build router
    let app = app(api_key_service, proxy_service, clerk).layer(cors);

    // Start server
    let addr = config.server_addr();
    let listener = TcpListener::bind(&addr).await?;
    info!("Server running on http://{}", addr);
    serve(listener, app).await?;

    Ok(())
}
