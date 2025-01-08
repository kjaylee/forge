CREATE TABLE IF NOT EXISTS configuration_table (
    id TEXT NOT NULL PRIMARY KEY,
    data TEXT NOT NULL,
    created_at TIMESTAMP NOT NULL,
    updated_at TIMESTAMP NOT NULL
);

-- Trigger to update the updated_at timestamp
CREATE TRIGGER IF NOT EXISTS update_configuration_timestamp 
    AFTER UPDATE ON configuration_table
BEGIN
    UPDATE configuration_table SET updated_at = CURRENT_TIMESTAMP WHERE provider_type = NEW.provider_type;
END;
