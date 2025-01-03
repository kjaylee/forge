CREATE TABLE conversations (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    created_at TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP,
    content TEXT NOT NULL  -- JSON serialized Request type
);

-- Trigger to update the updated_at timestamp
CREATE TRIGGER update_conversations_timestamp 
    AFTER UPDATE ON conversations
BEGIN
    UPDATE conversations SET updated_at = CURRENT_TIMESTAMP WHERE id = NEW.id;
END;
