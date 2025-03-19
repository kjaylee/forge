# Tool Description Improvement Plan

## Current State

The Code-Forge project currently implements tool descriptions for Claude using a two-part approach:

1. **Primary descriptions** via Rust doc comments above tool structs
2. **Parameter descriptions** via JsonSchema annotations on input types

These are combined at runtime by the `from()` implementation in `ToolDefinition`, which:
- Uses the doc comment as the main description
- Appends "Parameters:" followed by each parameter with its description
- Marks required parameters appropriately

Example from `fs_read.rs`:
```rust
/// Request to read the contents of a file at the specified path. Use this when
/// you need to examine the contents of an existing file you do not know the
/// contents of, for example to analyze code, review text files, or extract
/// information from configuration files. Automatically extracts raw text from
/// PDF and DOCX files. May not be suitable for other types of binary files, as
/// it returns the raw content as a string.
#[derive(ToolDescription)]
pub struct FSRead;
```

Parameter description from the same file:
```rust
#[derive(Deserialize, JsonSchema)]
pub struct FSReadInput {
    /// The path of the file to read, always provide absolute paths.
    pub path: String,
}
```

These combine into a complete description for Claude that covers both the tool's purpose and its parameters.

## Feedback on Current Descriptions

### Strengths

1. **Consistent Implementation**: All tools use the same pattern, ensuring uniformity
2. **Separation of Concerns**: Primary descriptions and parameter descriptions are defined separately
3. **Required Parameters**: Clearly marked in the final description 
4. **Length Validation**: Test ensures descriptions don't exceed maximum length
5. **Parameter Details**: Most parameter descriptions are thorough and clear

### Areas for Improvement

1. **Inconsistent Detail Level**: Some tool descriptions are comprehensive (like `fs_read`) while others are minimal
2. **Missing Usage Sections**: Not all descriptions explicitly state when to use/not use the tool
3. **Limited Error Information**: Few descriptions mention possible errors or how to handle them
4. **Few Examples**: Most descriptions lack concrete examples of proper usage
5. **Incomplete Limitations**: Some tools don't fully explain their limitations or constraints
6. **Alternatives Rarely Mentioned**: When a tool isn't appropriate, alternatives aren't consistently suggested

## Tool-Specific Feedback

### High-Quality Examples

`fs_read` has an excellent description that:
- Clearly states purpose
- Provides specific use cases
- Mentions limitations with binary files
- Explains what data is returned
- Has clear parameter description

### Needs Improvement

`fs_patch` (ApplyPatchJson) could be improved by:
- Adding examples of different operation types
- Explaining matching behavior (only exact matches)
- Clarifying when to use this vs. direct file write
- Describing behavioral details with multiple matches
- Adding error handling information

## Improvement Recommendations

### 1. Standardized Structure

Adopt a consistent structure for all tool descriptions with these sections:

```rust
/// [Tool Name]: [One-line summary of what it does]
///
/// ## Purpose
/// [Detailed explanation of the tool's function]
///
/// ## When to Use
/// [Specific scenarios where this tool is appropriate]
///
/// ## When NOT to Use
/// [Scenarios where this tool is not suitable, with alternatives]
///
/// ## Behavior Details
/// [Specific details about how the tool operates]
///
/// ## Limitations
/// [Constraints, caveats, and potential issues]
///
/// ## Error Handling
/// [Common errors and how to address them]
```

### 2. Enhanced Parameter Descriptions

Improve parameter descriptions with:
- Type information
- Value constraints
- Default values
- Examples of valid values

Example:
```rust
/// The path of the file to read. Must be an absolute path (starting with '/').
/// Relative paths will be rejected with an error.
/// Example: "/home/user/documents/file.txt"
pub path: String,
```

### 3. Example-Rich Descriptions

Add concrete examples for complex tools:

```rust
/// ## Examples
/// 
/// Replace text:
/// ```json
/// {
///   "path": "/path/to/file.txt",
///   "patches": [
///     {
///       "search": "old text",
///       "operation": "replace",
///       "content": "new text"
///     }
///   ]
/// }
/// ```
```

### 4. Clearly State Relationship Between Tools

Add context about tool relationships:
```rust
/// ## Related Tools
/// 
/// - Use `tool_forge_fs_read` to first examine file content
/// - Use `tool_forge_process_shell` for more complex file operations
/// - Consider `tool_forge_fs_create` for complete file rewrites
```

### 5. Tiered Implementation Approach

Prioritize improvements:

1. **High Priority** (Immediate improvements):
   - Add "When to Use" and "When NOT to Use" sections to all tools
   - Ensure all parameter descriptions include constraints and examples
   - Add error behavior to all descriptions

2. **Medium Priority**:
   - Add full standardized structure to highest-use tools
   - Enhance descriptions with examples for complex tools
   - Document tool relationships

3. **Lower Priority**:
   - Review and align all descriptions with standardized format
   - Add detailed behavior explanations for edge cases
   - Create comprehensive examples library

## Example Improved Description

Current `fs_patch` description:
```rust
/// Performs a single text operation (prepend, append, replace, swap, delete) on
/// matched text in a file. The operation is applied to the first match found in
/// the text.
```

Improved version:
```rust
/// Text Patch Tool: Performs precise text operations on specific matched content within a file
///
/// ## Purpose
/// Modifies file content by targeting exact text matches and performing operations like
/// prepend, append, replace, or swap. Designed for surgical text modifications without
/// rewriting entire files.
///
/// ## When to Use
/// - When you need to modify specific portions of a file while preserving the rest
/// - When you have exact text to match and modify
/// - For precise insertion or replacement operations
/// - When making the same change in multiple places using multiple patches
///
/// ## When NOT to Use
/// - When the target text varies or requires fuzzy matching (use regex with shell commands)
/// - For binary files or non-text content (use specialized tools)
/// - For moving or renaming files (use shell commands)
/// - For complete file rewrites (use tool_forge_fs_create instead)
///
/// ## Behavior Details
/// - Only performs exact text matching (no regex or fuzzy matching)
/// - Operations are applied to the first match found in each case
/// - Multiple patches are applied sequentially in the order provided
/// - Empty search text behaves specially: append/prepend target the file start/end
///
/// ## Limitations
/// - Cannot perform regex-based replacements
/// - No fuzzy matching for similar text
/// - Applies to first match only, not all matches
///
/// ## Error Handling
/// - Returns error if search text cannot be found
/// - Reports syntax warnings for code files when operations produce invalid syntax
/// - For swap operations, returns error if target swap text cannot be found
```

This improvement plan provides a clear path to enhancing tool descriptions that will make Claude more effective at selecting and using tools appropriately.