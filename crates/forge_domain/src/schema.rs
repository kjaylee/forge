use schemars::gen::{SchemaGenerator, SchemaSettings};
use schemars::schema::RootSchema;
use schemars::JsonSchema;

/// Generate a JSON schema for a type without the $schema field.
/// This is useful when you want to generate a clean schema without the
/// metadata.
#[macro_export]
macro_rules! schema_without_meta {
    ($t:ty) => {{
        let mut settings = ::schemars::gen::SchemaSettings::default();
        settings.meta_schema = None;
        let gen = ::schemars::gen::SchemaGenerator::new(settings);
        gen.into_root_schema_for::<$t>()
    }};
}

/// Utility function to generate a schema without metadata.
/// This is the function version of the `schema_without_meta` macro.
pub fn generate_schema_without_meta<T: JsonSchema>() -> RootSchema {
    let mut settings = SchemaSettings::default();
    settings.meta_schema = None;
    let gen = SchemaGenerator::new(settings);
    gen.into_root_schema_for::<T>()
}
