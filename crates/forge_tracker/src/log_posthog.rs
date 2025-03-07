use serde_json::json;
use tracing::span::{Attributes, Id, Record};
use tracing::{Event, Level, Subscriber};
use tracing_subscriber::layer::{Context, Layer};

use crate::{EventKind, Tracker};

/// A tracing layer that forwards log events to PostHog
pub struct PosthogLayer {
    tracker: &'static Tracker,
    min_level: Level,
}

impl PosthogLayer {
    pub fn new(tracker: &'static Tracker, min_level: Level) -> Self {
        Self { tracker, min_level }
    }
}

impl<S> Layer<S> for PosthogLayer
where
    S: Subscriber,
{
    fn on_event(&self, event: &Event<'_>, _ctx: Context<'_, S>) {
        // Extract metadata
        let meta = event.metadata();
        let level = *meta.level();

        // Skip events below the minimum level
        if level < self.min_level {
            return;
        }

        // Extract basic information about the event
        let target = meta.target();
        let file = meta.file();
        let line = meta.line();
        let module_path = meta.module_path();

        // Capture field values
        let mut visitor = JsonVisitor::default();
        event.record(&mut visitor);
        let fields = visitor.fields;

        // Create a JSON representation of the log event
        let log_data = json!({
            "level": level.as_str(),
            "target": target,
            "file": file,
            "line": line,
            "module_path": module_path,
            "fields": fields,
        });

        // Dispatch to PostHog
        // We're using fire-and-forget since we don't want logging to be blocking
        let tracker = self.tracker;
        let log_str = log_data.to_string();
        tokio::spawn(async move {
            let _ = tracker.dispatch(EventKind::Log(log_str)).await;
        });
    }

    // We don't need to implement span-related methods for basic logging
    fn on_new_span(&self, _: &Attributes<'_>, _: &Id, _: Context<'_, S>) {}
    fn on_record(&self, _: &Id, _: &Record<'_>, _: Context<'_, S>) {}
    fn on_follows_from(&self, _: &Id, _: &Id, _: Context<'_, S>) {}
    fn on_close(&self, _: Id, _: Context<'_, S>) {}
    fn on_enter(&self, _: &Id, _: Context<'_, S>) {}
    fn on_exit(&self, _: &Id, _: Context<'_, S>) {}
}

/// Custom visitor to collect field values as JSON
#[derive(Default)]
struct JsonVisitor {
    fields: serde_json::Map<String, serde_json::Value>,
}

impl tracing::field::Visit for JsonVisitor {
    fn record_debug(&mut self, field: &tracing::field::Field, value: &dyn std::fmt::Debug) {
        let value = format!("{:?}", value);
        self.fields.insert(field.name().to_string(), json!(value));
    }

    fn record_i64(&mut self, field: &tracing::field::Field, value: i64) {
        self.fields.insert(field.name().to_string(), json!(value));
    }

    fn record_u64(&mut self, field: &tracing::field::Field, value: u64) {
        self.fields.insert(field.name().to_string(), json!(value));
    }

    fn record_bool(&mut self, field: &tracing::field::Field, value: bool) {
        self.fields.insert(field.name().to_string(), json!(value));
    }

    fn record_str(&mut self, field: &tracing::field::Field, value: &str) {
        self.fields.insert(field.name().to_string(), json!(value));
    }

    fn record_error(
        &mut self,
        field: &tracing::field::Field,
        value: &(dyn std::error::Error + 'static),
    ) {
        self.fields
            .insert(field.name().to_string(), json!(value.to_string()));
    }
}
