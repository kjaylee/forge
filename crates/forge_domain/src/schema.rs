/// Generate a JSON schema for a type without the `$schema` field.
#[macro_export]
macro_rules! json_schema {
    ($t:ty) => {{
        let mut settings = ::schemars::gen::SchemaSettings::default();
        settings.meta_schema = None;
        let gen = ::schemars::gen::SchemaGenerator::new(settings);
        gen.into_root_schema_for::<$t>()
    }};
}


#[cfg(test)]
mod tests {
    use schemars::JsonSchema;

    #[test]
    fn test(){
        #[derive(JsonSchema)]
        struct Test {
            _name: String,
        }
        insta::assert_snapshot!(serde_json::to_string_pretty(&json_schema!(Test)).unwrap());
    }
}