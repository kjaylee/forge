mod config;
mod conversation;
mod learning;

pub use config::{ConfigRepository, Live as ConfigRepositoryLive};
pub use conversation::{ConversationRepository, Live as ConversationRepositoryLive};
pub use learning::Live as LearningRepositoryLive;

#[cfg(test)]
pub mod tests {
    pub use super::config::tests::TestStorage as TestConfigStorage;
    pub use super::conversation::tests::TestStorage as TestConversationStorage;
    pub use super::learning::tests::TestStorage as TestLearningStorage;
}
