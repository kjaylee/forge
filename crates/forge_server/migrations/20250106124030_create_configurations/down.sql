-- This file should undo anything in `up.sql`

DROP TRIGGER IF EXISTS update_configuration_timestamp;
DROP TABLE configuration_table;
