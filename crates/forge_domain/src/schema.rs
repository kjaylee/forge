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
