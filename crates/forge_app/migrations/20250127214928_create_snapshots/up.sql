CREATE TABLE IF NOT EXISTS snapshots (
    id TEXT PRIMARY KEY NOT NULL,
    created_at TIMESTAMP NOT NULL,
    updated_at TIMESTAMP NOT NULL,
    file_path TEXT NOT NULL,
    archived BOOLEAN NOT NULL DEFAULT false,
    snapshot_path TEXT NOT NULL
);

-- Trigger to update the updated_at timestamp
CREATE TRIGGER update_snapshots_timestamp 
    AFTER UPDATE ON snapshots
    FOR EACH ROW
    BEGIN
        UPDATE snapshots SET updated_at = CURRENT_TIMESTAMP WHERE id = NEW.id;
    END;