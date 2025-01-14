-- Your SQL goes here

CREATE TABLE learning_table (
    id TEXT PRIMARY KEY NOT NULL,
    conversation_id TEXT NOT NULL,
    learnings TEXT NOT NULL,
    created_at TIMESTAMP NOT NULL,
    FOREIGN KEY (conversation_id) REFERENCES conversations(id)
);
