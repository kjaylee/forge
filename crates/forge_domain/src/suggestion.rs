use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub struct Suggestion {
    pub actual_user_message: String,
    pub enriched_user_message: String,
    pub suggestion: String,
}
