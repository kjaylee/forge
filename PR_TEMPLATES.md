# Pull Request Templates & Standards

This document outlines standards for creating effective Pull Requests and provides templates to ensure consistency across contributions.

## PR Creation Guidelines

### PR Title Format
- Use conventional commit format: `type(scope): short description`
- Types include: feat, fix, docs, style, refactor, test, chore
- Keep titles concise but descriptive (< 70 characters)

### PR Description Components
- **Overview:** Brief summary of the change
- **Changes:** List of specific modifications
- **Testing:** How the changes were tested
- **Related Issues:** Link to any related GitHub issues

## PR Templates

### Feature Template
```md
## Overview
Brief description of the feature

## Changes
- List of specific implementation details
- Technical approach used

## Testing
- Tests added/modified
- How to verify functionality

## Related Issues
Fixes #issue_number
```

### Bug Fix Template
```md
## Overview
Description of the bug and fix

## Root Cause
What caused the bug

## Fix Details
How the fix addresses the root cause

## Testing
- Steps to verify the fix
- Regression tests added

## Related Issues
Fixes #issue_number
```

## Review Standards
- All PRs should have at least one review before merging
- Code style and quality standards must be maintained
- Automated checks must pass (tests, linting, etc.)
- Significant changes should include documentation updates