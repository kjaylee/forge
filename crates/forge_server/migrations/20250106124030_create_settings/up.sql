-- Your SQL goes here

CREATE TABLE settings (
    id TEXT NOT NULL,
    project_path TEXT NOT NULL,
    chosen_model TEXT NOT NULL,
    created_at TIMESTAMP NOT NULL,
    updated_at TIMESTAMP NOT NULL,
    PRIMARY KEY (id)
);

-- Trigger to update the updated_at timestamp
CREATE TRIGGER IF NOT EXISTS update_settings_timestamp 
    AFTER UPDATE ON settings
BEGIN
    UPDATE settings SET updated_at = CURRENT_TIMESTAMP WHERE id = NEW.id;
END;
