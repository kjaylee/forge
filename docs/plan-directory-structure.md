# Plan Directory Structure Guide

## Overview

This document describes the new organization of plan files in the project, using a date-based directory structure with versioning.

## Directory Structure

Plans are now organized with the following structure:

```
plans/
├── YYYY-MM-DD/
│   ├── task-name-v0.md
│   ├── task-name-v1.md
│   └── another-task-v0.md
└── YYYY-MM-DD/
    └── task-name-v0.md
```

Where:
- `YYYY-MM-DD` is the date the plan was created
- `task-name` is a hyphenated name describing the task
- `vN` is the version number of the plan (v0, v1, v2, etc.), with v0 representing initial drafts

## Creating Plans

When creating a new plan:

1. Create a directory for the current date if it doesn't exist
2. Name your plan file using the convention `task-name-v0.md`
3. If you update a plan, increment the version number (v1, v2, etc.)

### Manual Creation

```bash
# Create the date directory (if it doesn't exist)
mkdir -p plans/$(date +"%Y-%m-%d")

# Create the plan file
touch plans/$(date +"%Y-%m-%d")/task-name-v0.md
```

### Using the Helper Script

Alternatively, use the provided helper script:

```bash
./create-plan.sh task-name [version]
```

The script will:
- Create the date directory if it doesn't exist
- Create a plan file with a template
- Name the file appropriately with the current date and version

## Examples

Here are examples of plan files created with this structure:

- `plans/2025-03-30/authentication-system-v0.md` - Initial draft for authentication system
- `plans/2025-03-30/authentication-system-v1.md` - Updated plan after review
- `plans/2025-03-30/api-rate-limiting-v0.md` - Initial draft for API rate limiting
- `plans/2025-04-01/microservices-migration-v0.md` - Initial draft for microservices migration

## Benefits

This directory structure provides several benefits:

1. **Organization by date** - Easy to find plans created on a specific date
2. **Clear versioning** - Multiple versions of the same plan are clearly identified
3. **Simple navigation** - Clear directory structure makes it easy to find specific plans
4. **Implementation history** - Provides a chronological view of planning activities