--------------------------- MODULE REQ_STATE_002 ---------------------------
(* 
REQ-STATE-002: Verify Task Existence
This module specifies the requirement that the system shall verify that a 
specified task ID exists in the system before attempting to mark it as complete.

Acceptance Criteria:
- Invalid task IDs are rejected with error message "❌ Error: Task not found"
- Valid task IDs proceed to task completion operation
- No state changes occur for non-existent tasks

Key Invariants:
- System data integrity must be maintained

Execution Context:
- User must invoke the "todo done [task_id]" command
- Must occur after command invocation
- Must occur before marking task as complete

This is a read-only operation that does not change system state, but serves
as a validation gate before task completion operations.
*)

EXTENDS Integers, Sequences, FiniteSets

\* Constants
CONSTANTS 
    TaskIds,        \* Set of all possible task IDs
    ERROR_MESSAGE   \* Error message for invalid task IDs

VARIABLES
    existingTasks,  \* Set of task IDs that exist in the system
    message,        \* Output message to the user
    verificationSucceeded  \* Boolean flag indicating if verification succeeded

vars == <<existingTasks, message, verificationSucceeded>>

\* Type invariant
TypeOK ==
    /\ existingTasks ⊆ TaskIds
    /\ message ∈ [type: {"success", "error"}, content: STRING] ∪ {<<>>}
    /\ verificationSucceeded ∈ BOOLEAN

\* Initial state
Init ==
    /\ existingTasks ⊆ TaskIds  \* Some subset of all possible task IDs exist
    /\ message = <<>>          \* No message initially
    /\ verificationSucceeded = FALSE

\* Action: Verify that a task exists
VerifyTaskExists(taskId) ==
    /\ IF taskId ∈ existingTasks
       THEN 
           /\ verificationSucceeded' = TRUE
           /\ message' = <<>>  \* No error message needed
       ELSE
           /\ verificationSucceeded' = FALSE
           /\ message' = [type |-> "error", content |-> ERROR_MESSAGE]
    /\ UNCHANGED <<existingTasks>>  \* This is a read-only operation

\* The next-state relation
Next ==
    \E taskId ∈ TaskIds: VerifyTaskExists(taskId)

\* The complete specification
Spec == Init /\ [][Next]_vars

\* INVARIANTS

\* System data integrity must be maintained
DataIntegrityInvariant ==
    /\ existingTasks ⊆ TaskIds
    /\ \A taskId ∈ TaskIds: 
        (taskId ∈ existingTasks) => (taskId ∈ TaskIds)

\* PROPERTIES

\* Invalid task IDs are rejected with error message
InvalidTasksRejected ==
    \A taskId ∈ TaskIds:
        (taskId ∉ existingTasks) => 
            (VerifyTaskExists(taskId) => (message' = [type |-> "error", content |-> ERROR_MESSAGE]))

\* Valid task IDs proceed to task completion operation
ValidTasksProceeded ==
    \A taskId ∈ TaskIds:
        (taskId ∈ existingTasks) => 
            (VerifyTaskExists(taskId) => verificationSucceeded')

\* No state changes occur for non-existent tasks
NoStateChangesForNonExistentTasks ==
    \A taskId ∈ TaskIds:
        (taskId ∉ existingTasks) => 
            (VerifyTaskExists(taskId) => (existingTasks' = existingTasks))

\* THEOREMS
\* The specification satisfies all required properties
THEOREM Spec => []DataIntegrityInvariant

=============================================================================