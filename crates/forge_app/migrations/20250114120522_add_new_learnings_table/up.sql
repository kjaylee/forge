CREATE TABLE IF NOT EXISTS learning_table (
    id TEXT PRIMARY KEY NOT NULL,
    cwd TEXT NOT NULL,
    learnings TEXT NOT NULL,
    created_at TIMESTAMP NOT NULL,
    updated_at TIMESTAMP NOT NULL
);