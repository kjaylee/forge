// @generated automatically by Diesel CLI.

diesel::table! {
    conversations (id) {
        id -> Text,
        created_at -> Timestamp,
        updated_at -> Timestamp,
        content -> Text,
        archived -> Bool,
    }
}

diesel::table! {
    settings (id) {
        id -> Text,
        project_path -> Text,
        chosen_model -> Text,
        created_at -> Timestamp,
        updated_at -> Timestamp,
    }
}

diesel::allow_tables_to_appear_in_same_query!(conversations, settings,);
