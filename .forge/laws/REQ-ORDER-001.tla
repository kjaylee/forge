------------------------------ MODULE TaskCompletionSequence ------------------------------
(*
 * TLA+ Specification for REQ-ORDER-001: Operation Sequence Enforcement
 *
 * Requirement: The system shall enforce the operational sequence of verifying task 
 * existence, marking task as complete, sending notification, and displaying feedback.
 *
 * Acceptance Criteria:
 * - Operations execute in the required sequence
 * - Later operations do not execute if earlier operations fail
 * - All successful operations in the sequence complete with no exceptions
 * 
 * Temporal Invariants:
 * - No operation in the sequence can be skipped or executed out of order
 *)

EXTENDS Naturals, Sequences

(* ---------------------------------- CONSTANTS ---------------------------------- *)

\* Set of possible task identifiers
CONSTANT TaskID

\* Set of all possible operation outcomes 
CONSTANT Outcome, FailReason
ASSUME Outcome = {"Success", "Failure"}

\* Return/feedback types for each operation
CONSTANT 
    TaskExistenceResult,     \* Return type of VerifyTaskExists
    MarkCompleteResult,      \* Return type of MarkTaskComplete
    NotificationResult,      \* Return type of SendNotification
    FeedbackResult          \* Return type of DisplayFeedback

(* ---------------------------------- VARIABLES ---------------------------------- *)

VARIABLES
    stepPhase,       \* Current phase of the task completion operation
    taskId,          \* ID of the task currently being processed
    operationResult, \* Result of the current operation
    taskExists,      \* Whether the task with ID taskId exists
    completionStatus \* Whether the task with ID taskId is completed

\* All variables grouped for use in next-state relation
vars == <<stepPhase, taskId, operationResult, taskExists, completionStatus>>

(* ------------------------------ TYPE INVARIANTS ------------------------------ *)

ValidStepPhase == 
    stepPhase \in {"Idle", "VerifyTaskExists", "MarkTaskComplete", 
                  "SendNotification", "DisplayFeedback", "Complete", "Failed"}

ValidTaskId ==
    taskId \in TaskID \union {NULL}
    
ValidOperationResult ==
    operationResult \in [outcome: Outcome, 
                         reason: FailReason \union {NULL},
                         details: TaskExistenceResult \union MarkCompleteResult \union 
                                 NotificationResult \union FeedbackResult \union {NULL}]

TypeOK ==
    /\ ValidStepPhase
    /\ ValidTaskId
    /\ ValidOperationResult
    /\ taskExists \in BOOLEAN
    /\ completionStatus \in BOOLEAN

(* ------------------------------ INITIAL STATE ------------------------------ *)

Init ==
    /\ stepPhase = "Idle"
    /\ taskId = NULL
    /\ operationResult = [outcome |-> "Success", reason |-> NULL, details |-> NULL]
    /\ taskExists = FALSE
    /\ completionStatus = FALSE

(* ------------------------------ OPERATIONS ------------------------------ *)

\* Begin the task completion sequence with a given task ID
StartTaskCompletion(id) ==
    /\ stepPhase = "Idle"
    /\ taskId' = id
    /\ stepPhase' = "VerifyTaskExists"
    /\ UNCHANGED <<operationResult, taskExists, completionStatus>>

\* Verify if the task exists
VerifyTaskExists ==
    /\ stepPhase = "VerifyTaskExists"
    /\ \/ /\ taskExists' = TRUE  \* Task exists case
          /\ operationResult' = [outcome |-> "Success", 
                               reason |-> NULL, 
                               details |-> "TaskVerified"]
          /\ stepPhase' = "MarkTaskComplete"
       \/ /\ taskExists' = FALSE  \* Task does not exist case
          /\ operationResult' = [outcome |-> "Failure", 
                               reason |-> "TaskDoesNotExist", 
                               details |-> "TaskNotFound"]
          /\ stepPhase' = "Failed"
    /\ UNCHANGED <<taskId, completionStatus>>

\* Mark the task as complete
MarkTaskComplete ==
    /\ stepPhase = "MarkTaskComplete"
    /\ taskExists = TRUE  \* Precondition: task must exist
    /\ \/ /\ completionStatus' = TRUE  \* Success case
          /\ operationResult' = [outcome |-> "Success", 
                               reason |-> NULL, 
                               details |-> "TaskMarkedComplete"]
          /\ stepPhase' = "SendNotification"
       \/ /\ operationResult' = [outcome |-> "Failure", 
                               reason |-> "MarkCompleteError", 
                               details |-> "ErrorUpdatingTask"]
          /\ stepPhase' = "Failed"  
          /\ UNCHANGED completionStatus
    /\ UNCHANGED <<taskId, taskExists>>

\* Send notification about task completion
SendNotification ==
    /\ stepPhase = "SendNotification"
    /\ taskExists = TRUE
    /\ completionStatus = TRUE  \* Precondition: task must be marked complete
    /\ \/ /\ operationResult' = [outcome |-> "Success", 
                               reason |-> NULL, 
                               details |-> "NotificationSent"]
          /\ stepPhase' = "DisplayFeedback"
       \/ /\ operationResult' = [outcome |-> "Failure", 
                               reason |-> "NotificationError", 
                               details |-> "ErrorSendingNotification"]
          /\ stepPhase' = "Failed"
    /\ UNCHANGED <<taskId, taskExists, completionStatus>>

\* Display feedback to the user
DisplayFeedback ==
    /\ stepPhase = "DisplayFeedback"
    /\ \/ /\ operationResult' = [outcome |-> "Success", 
                               reason |-> NULL, 
                               details |-> "FeedbackDisplayed"]
          /\ stepPhase' = "Complete"
       \/ /\ operationResult' = [outcome |-> "Failure", 
                               reason |-> "FeedbackError", 
                               details |-> "ErrorDisplayingFeedback"]
          /\ stepPhase' = "Failed"
    /\ UNCHANGED <<taskId, taskExists, completionStatus>>

\* Reset the system to the idle state
ResetSystem ==
    /\ stepPhase \in {"Complete", "Failed"}
    /\ stepPhase' = "Idle"
    /\ taskId' = NULL
    /\ operationResult' = [outcome |-> "Success", reason |-> NULL, details |-> NULL]
    /\ taskExists' = FALSE
    /\ completionStatus' = FALSE

(* ------------------------------ STATE TRANSITIONS ------------------------------ *)

Next ==
    \/ \E id \in TaskID: StartTaskCompletion(id)
    \/ VerifyTaskExists
    \/ MarkTaskComplete
    \/ SendNotification
    \/ DisplayFeedback
    \/ ResetSystem

(* ------------------------------ SPECIFICATION ------------------------------ *)

Spec == 
    /\ Init 
    /\ [][Next]_vars
    /\ WF_vars(Next)  \* Weak fairness ensures the sequence eventually completes

(* ------------------------------ INVARIANTS ------------------------------ *)

\* No operation can be skipped or executed out of order
OperationOrderPreserved ==
    [](
        /\ (stepPhase = "MarkTaskComplete") => (operationResult.details = "TaskVerified")
        /\ (stepPhase = "SendNotification") => (operationResult.details = "TaskMarkedComplete")
        /\ (stepPhase = "DisplayFeedback") => (operationResult.details = "NotificationSent")
        /\ (stepPhase = "Complete") => (operationResult.details = "FeedbackDisplayed")
    )

\* If an operation fails, the sequence enters the Failed state
OperationFailureHandling ==
    [](
        (operationResult.outcome = "Failure") => <>(stepPhase = "Failed")
    )

\* The entire sequence completes successfully if all operations succeed
SuccessfulCompletion ==
    []((stepPhase = "Idle") ~> 
        ((stepPhase = "Complete") \/ (stepPhase = "Failed")))

\* Tasks cannot be marked complete unless they exist
TaskExistenceBeforeCompletion ==
    [](completionStatus = TRUE => taskExists = TRUE)

(* ------------------------------ THEOREMS ------------------------------ *)

THEOREM Spec => []TypeOK
THEOREM Spec => OperationOrderPreserved
THEOREM Spec => OperationFailureHandling
THEOREM Spec => SuccessfulCompletion
THEOREM Spec => TaskExistenceBeforeCompletion

=============================================================================
\* Modification History
\* Last modified: Task Completion Sequence Enforcement Specification