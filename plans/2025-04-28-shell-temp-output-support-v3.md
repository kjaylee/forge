# Support for Large Shell Command Outputs via Temp Files (v3)

## Objective
Enhance the shell command tool to handle large output by creating temporary files that can be read later, with all logic consolidated within the shell tool implementation. This will prevent memory issues and UI delays when dealing with commands that produce extensive output, while maintaining a simpler architecture.

## Implementation Plan

1. **Design a new Shell Output Storage Model**
   - Dependencies: None
   - Notes: Creates a new domain type for shell outputs that supports both direct and file-based access
   - Files:
     - `crates/forge_domain/src/shell.rs`
   - Status: Not Started

2. **Update CommandOutput struct**
   - Dependencies: Task 1
   - Notes: Extend to handle potential temp file paths and metadata
   - Files:
     - `crates/forge_domain/src/shell.rs`
   - Status: Not Started

3. **Implement Temp File Management in Shell Tool**
   - Dependencies: Task 1, Task 2
   - Notes: 
     - Add private functions in shell tool to handle temp file operations
     - Include file creation, reading, and cleanup logic
     - Implement file rotation and management directly in the shell tool
   - Files:
     - `crates/forge_services/src/tools/shell.rs`
   - Status: Not Started

4. **Modify Shell Tool Format Output Function**
   - Dependencies: Task 2, Task 3
   - Notes: 
     - Update to detect large outputs and use temp files
     - Modify the returned `ToolResult` to indicate that output is stored in a file
     - Provide metadata and partial content in the response
     - **Example Formatted Output for Large Results:**
       ```text
       ---
       command:'/bin/ls -lR /' 
       exit_code: 0
       command_output_path: /tmp/forge_shell_output_abc789.tmp
       stdout_total_chars: 10000
       stderr_total_chars: 0      
       ---
       <stdout char_range="0-500">
       [...]
       </stdout>
       
       <stdout char_range="9500-10000">
       [...]
       </stdout>

       <stderr>
       </stderr>

       ```
   - Files:
     - `crates/forge_services/src/tools/shell.rs`
   - Status: Not Started

5. **Modify Command Executor Service**
   - Dependencies: Task 2
   - Notes: Update to support writing to temp files for large outputs
   - Files:
     - `crates/forge_infra/src/executor.rs`
   - Status: Not Started

6. **Add Size Threshold Configuration**
   - Dependencies: None
   - Notes: Add configurable threshold for when to use temp files
   - Files:
     - `crates/forge_domain/src/env.rs`
   - Status: Not Started

7. **Implement Temp File Discovery Mechanism**
   - Dependencies: Task 3
   - Notes: Add functionality to list and manage previously created temp output files
   - Files:
     - `crates/forge_services/src/tools/shell.rs`
   - Status: Not Started

8. **Add File Rotation and Cleanup Logic**
   - Dependencies: Task 3
   - Notes: Ensure proper management of temp files over time
   - Files:
     - `crates/forge_services/src/tools/shell.rs`
   - Status: Not Started

9. **Add Unit Tests**
   - Dependencies: All previous tasks
   - Notes: Comprehensive tests for new functionality
   - Files:
     - `crates/forge_services/src/tools/shell.rs`
     - `crates/forge_infra/src/executor.rs`
   - Status: Not Started

## Verification Criteria
- Shell commands producing large outputs (>1MB) should store results in temp files
- Temp files should be properly managed (created, accessed, and cleaned up)
- Output format in temp files should maintain the same structure as direct output
- UI should display appropriate messages when output is stored in a file
- Tests should verify all edge cases (large output, binary content, file cleanup)
- Performance should improve for commands with extensive output
- Disk space should be managed with file rotation policies
- Old temp files should be automatically cleaned up

## Potential Risks and Mitigations

1. **Code Organization and Complexity**
   Mitigation: Use clear code organization with private helper functions and comments to maintain readability in the shell tool

2. **Temp File Management**
   Mitigation: Implement robust cleanup mechanisms directly in the shell tool using tempfile crate

3. **Binary Data Handling**
   Mitigation: Use Base64 encoding for binary data and include content-type metadata

4. **Cross-platform Compatibility**
   Mitigation: Use platform-independent path handling and test on multiple operating systems

5. **Race Conditions**
   Mitigation: Implement proper synchronization for file access and atomic file operations

6. **Performance Impact**
   Mitigation: Only use temp files for outputs exceeding the configured threshold

7. **Disk Space Exhaustion**
   Mitigation: Implement file rotation with configurable retention policies

8. **File Permission Issues**
   Mitigation: Handle permission errors gracefully with detailed error messages

9. **Interrupted Commands**
   Mitigation: Ensure partial outputs are properly handled and temp files are cleaned up

10. **Large Number of Files**
    Mitigation: Implement file grouping and indexing for better management

## Edge Cases to Handle

1. **Commands with Continuous Output**
   - Implement streaming write mechanism for commands producing output continuously
   - Support appending to temp files without loading entire content

2. **Partially Binary Outputs**
   - Detect binary content in outputs and handle encoding/decoding appropriately
   - Store content type metadata for proper display

3. **Temporary Directory Unavailable**
   - Implement fallback mechanisms when temp directory is unavailable
   - Handle permission issues with meaningful error messages

4. **Concurrent Command Execution**
   - Ensure temp file naming prevents conflicts during concurrent execution
   - Implement proper resource locking where needed

5. **Long-running Sessions**
   - Implement file rotation policies for disk space management
   - Add background cleanup jobs for orphaned temp files

6. **Machine Crashes or Program Termination**
   - Include recovery mechanism for orphaned temp files
   - Use session identifiers in file names for better tracking

7. **Output Format Detection**
   - Preserve specialized output formats (JSON, XML, etc.)
   - Add content-type awareness for better display

8. **Cross-Platform File Path Handling**
   - Use platform-independent path construction
   - Test file paths on Windows, macOS, and Linux

## Alternative Approaches

1. **Pure Stream Processing**: Process output in chunks without any storage, forwarding directly to UI. More complex but eliminates storage concerns.

2. **Intelligent Truncation**: Implement smart truncation that preserves important parts (start, end, error messages) when truncating large outputs.

3. **Compressed Storage**: Use on-the-fly compression for outputs, reducing disk space usage for very large outputs.

4. **Hybrid Approach**: Use in-memory for small outputs, temp files for medium outputs, and specialized storage for very large outputs.

5. **Output Reference Approach**: Instead of creating a separate reader tool, provide file paths in the output that can be accessed by existing file system tools when needed.
