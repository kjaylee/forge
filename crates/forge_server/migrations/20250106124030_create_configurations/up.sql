CREATE TABLE IF NOT EXISTS configurations (
    provider_type TEXT NOT NULL CHECK (provider_type IN ('primary', 'secondary')) PRIMARY KEY,
    provider_id TEXT NOT NULL,
    model_id TEXT NOT NULL,
    api_key TEXT,
    created_at TIMESTAMP NOT NULL,
    updated_at TIMESTAMP NOT NULL
);

-- Trigger to update the updated_at timestamp
CREATE TRIGGER IF NOT EXISTS update_configuration_timestamp 
    AFTER UPDATE ON configurations
BEGIN
    UPDATE configurations SET updated_at = CURRENT_TIMESTAMP WHERE provider_type = NEW.provider_type;
END;
