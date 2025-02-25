use forge_gateway::config::Config;
use forge_gateway::ForgeGateway;
use shuttle_runtime::SecretStore;

#[shuttle_runtime::main]
async fn main(#[shuttle_runtime::Secrets] secret_store: SecretStore) -> shuttle_axum::ShuttleAxum {
    // load the secrets into the present environment.
    secret_store.into_iter().for_each(|(key, val)| {
        std::env::set_var(key, val);
    });

    let gateway_config = Config::from_env()?;
    let router = ForgeGateway::init(gateway_config);
    Ok(router.into())
}
