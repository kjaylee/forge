// @generated automatically by Diesel CLI.

diesel::table! {
    configurations (provider_type) {
        provider_type -> Text,
        provider_id -> Text,
        model_id -> Text,
        api_key -> Nullable<Text>,
        created_at -> Timestamp,
        updated_at -> Timestamp,
    }
}

diesel::table! {
    conversations (id) {
        id -> Text,
        created_at -> Timestamp,
        updated_at -> Timestamp,
        content -> Text,
        archived -> Bool,
    }
}

diesel::allow_tables_to_appear_in_same_query!(configurations, conversations,);
