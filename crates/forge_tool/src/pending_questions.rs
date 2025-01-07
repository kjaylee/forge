use std::collections::HashMap;
use std::sync::Arc;

use tokio::sync::{broadcast, oneshot, RwLock};

use crate::ask::{AgentQuestion, Question};

/// Manages pending questions waiting for user responses
pub struct PendingQuestions {
    pub sender: broadcast::Sender<AgentQuestion>,
    pub questions: Arc<RwLock<HashMap<String, oneshot::Sender<String>>>>,
}

impl Default for PendingQuestions {
    fn default() -> Self {
        let (sender, _) = broadcast::channel(1);
        Self { sender, questions: Arc::new(RwLock::new(HashMap::new())) }
    }
}

impl PendingQuestions {
    pub async fn submit_question(
        &self,
        question: &Question,
    ) -> Result<oneshot::Receiver<String>, String> {
        let (tx, rx) = oneshot::channel();
        let question: AgentQuestion = question.try_into()?;
        self.questions.write().await.insert(question.id.clone(), tx);

        // Send the question to the client.
        self.sender.send(question).expect("Failed to send question");

        Ok(rx)
    }

    /// Submit an answer for a question by its ID
    pub async fn submit_answer(&self, id: String, answer: String) -> Result<(), String> {
        let mut questions = self.questions.write().await;
        if let Some(tx) = questions.remove(&id) {
            tx.send(answer)
                .map_err(|_| "Failed to send answer".to_string())
        } else {
            Err("Question not found".to_string())
        }
    }
}
