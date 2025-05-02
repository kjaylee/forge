use merge::Merge;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum UpdateFrequency {
    #[serde(rename = "daily")]
    Daily,
    #[serde(rename = "weekly")]
    Weekly,
    #[serde(rename = "never")]
    Never,
}

impl From<String> for UpdateFrequency {
    fn from(value: String) -> Self {
        match value.as_str() {
            "daily" => UpdateFrequency::Daily,
            "weekly" => UpdateFrequency::Weekly,
            _ => UpdateFrequency::Never,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, Merge, Default)]
pub struct Update {
    pub check_frequency: Option<UpdateFrequency>,
    pub auto_update: Option<bool>,
}

pub fn update_config(base: &mut Option<Update>, other: Option<Update>) {
    if let Some(other) = other {
        // create a new update config
        let mut update = Update::default();

        // only update the values that are set in the other config
        update.auto_update = if other.auto_update.is_some() {
            other.auto_update
        } else {
            base.clone().unwrap().auto_update
        };

        update.check_frequency = if other.check_frequency.is_some() {
            other.check_frequency
        } else {
            base.clone().unwrap().check_frequency
        };

        // apply merged config to the base config
        *base = Some(update);
    }
}
