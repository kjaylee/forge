use std::path::PathBuf;

use tracing::debug;
use tracing_appender::non_blocking::WorkerGuard;
use tracing_subscriber::fmt::format::FmtSpan;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{self};

pub fn init_tracing(log_path: PathBuf) -> anyhow::Result<Guard> {
    debug!(path = %log_path.display(), "Initializing logging system in JSON format");

    let append = tracing_appender::rolling::daily(log_path, "forge.log");
    let (non_blocking, guard) = tracing_appender::non_blocking(append);

    tracing_subscriber::fmt()
        .json()
        .with_env_filter(
            tracing_subscriber::EnvFilter::try_from_env("FORGE_LOG")
                .unwrap_or_else(|_| tracing_subscriber::EnvFilter::new("forge=debug")),
        )
        .with_timer(tracing_subscriber::fmt::time::uptime())
        .with_thread_ids(false)
        .with_target(true)
        .with_file(true)
        .with_line_number(true)
        .with_ansi(true)
        .with_span_events(FmtSpan::ACTIVE)
        .with_writer(non_blocking)
        .init();

    debug!("JSON logging system initialized successfully");
    Ok(Guard(guard))
}

pub fn init_tracing_with_posthog(
    log_path: PathBuf,
    tracker: &'static crate::Tracker,
) -> anyhow::Result<Guard> {
    debug!(path = %log_path.display(), "Initializing logging system with PostHog integration");

    let append = tracing_appender::rolling::daily(log_path, "forge.log");
    let (non_blocking, guard) = tracing_appender::non_blocking(append);

    let posthog_layer = crate::PosthogLayer::new(tracker, tracing::Level::INFO);

    tracing_subscriber::registry()
        .with(posthog_layer)
        .with(
            tracing_subscriber::fmt::layer()
                .json()
                .with_timer(tracing_subscriber::fmt::time::uptime())
                .with_thread_ids(false)
                .with_target(true)
                .with_file(true)
                .with_line_number(true)
                .with_ansi(true)
                .with_writer(non_blocking),
        )
        .with(
            tracing_subscriber::EnvFilter::try_from_env("FORGE_LOG")
                .unwrap_or_else(|_| tracing_subscriber::EnvFilter::new("forge=debug")),
        )
        .init();

    debug!("Logging system with PostHog integration initialized successfully");
    Ok(Guard(guard))
}

pub struct Guard(#[allow(dead_code)] WorkerGuard);
