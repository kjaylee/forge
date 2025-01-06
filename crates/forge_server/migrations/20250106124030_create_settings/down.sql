-- This file should undo anything in `up.sql`

DROP TRIGGER IF EXISTS update_settings_timestamp;
DROP TABLE settings;
