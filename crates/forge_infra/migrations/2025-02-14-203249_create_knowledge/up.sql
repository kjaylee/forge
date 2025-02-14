-- Create knowledge table
CREATE TABLE
    knowledge (
        id INTEGER PRIMARY KEY NOT NULL,
        content TEXT NOT NULL,
        encoding TEXT NOT NULL,
        created_at TIMESTAMP NOT NULL,
        updated_at TIMESTAMP NOT NULL
    );