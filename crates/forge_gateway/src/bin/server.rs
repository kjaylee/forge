use std::sync::Arc;

use clerk_rs::clerk::Clerk;
use clerk_rs::validators::authorizer::ClerkAuthorizer;
use clerk_rs::ClerkConfiguration;
use forge_gateway::config::Config;
use forge_gateway::presentation::routes::app;
use forge_gateway::service::{ApiKeyService, ProxyService};
use forge_gateway::{ApiKeyRepositoryImpl, ClerkAuthorizeService, KeyGeneratorServiceImpl};
use forge_open_router::ProviderBuilder;
use postgrest::Postgrest;
use shuttle_runtime::SecretStore;
use tower_http::cors::{Any, CorsLayer};

#[shuttle_runtime::main]
async fn axum(#[shuttle_runtime::Secrets] secret_store: SecretStore) -> shuttle_axum::ShuttleAxum {
    // Load secrets into environment variables
    secret_store.into_iter().for_each(|(key, val)| {
        std::env::set_var(key, val);
    });

    // Load configuration from Shuttle secrets
    let config = Config::from_env();

    // Setup provider
    let provider = ProviderBuilder::from_url(config.provider_url.clone())
        .with_key(config.provider_key.clone())
        .build()
        .expect("Failed to build provider");

    // Initialize Supabase client
    let client = Postgrest::new(&config.supabase_url).insert_header("apikey", &config.supabase_key);

    // Initialize dependencies
    let key_gen_service = Arc::new(KeyGeneratorServiceImpl::new(
        config.api_key_length as usize,
        &config.api_key_prefix,
    ));
    let api_key_repository_impl = Arc::new(ApiKeyRepositoryImpl::new(client));
    let api_key_service = Arc::new(ApiKeyService::new(api_key_repository_impl, key_gen_service));
    let proxy_service = Arc::new(ProxyService::new(provider));

    // Initialize Clerk auth
    let clerk_config =
        ClerkConfiguration::new(None, None, Some(config.clerk_secret_key.clone()), None);
    let auth_service = Arc::new(ClerkAuthorizeService::new(ClerkAuthorizer::new(
        Clerk::new(clerk_config),
        true,
    )));

    // Create CORS layer
    let cors = CorsLayer::new()
        .allow_methods(Any)
        .allow_headers(Any)
        .allow_origin(Any);

    // Build router
    let app = app(api_key_service, proxy_service, auth_service).layer(cors);

    Ok(app.into())
}
