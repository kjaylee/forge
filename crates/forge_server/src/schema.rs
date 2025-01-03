// @generated automatically by Diesel CLI.

diesel::table! {
    conversations (id) {
        id -> Integer,
        created_at -> Timestamp,
        updated_at -> Timestamp,
        content -> Text,  // Will be deserialized into Request type
    }
}
