----------------------------- MODULE REQ_STATE_003 -----------------------------
(* REQ-STATE-003: Provide Completion Feedback *)

EXTENDS Naturals, Sequences, FiniteSets

\* CONSTANTS
TaskIDs == 1..10  \* Assume a finite set of possible task IDs for simplicity
TaskDescriptions == {"Task 1", "Task 2", "Task 3", "Task 4", "Task 5"}  \* Sample task descriptions

\* VARIABLES
VARIABLES
    taskCompletionOperationStatus,  \* Status of the task completion operation
    displayedFeedback,              \* The feedback currently displayed to the user
    notificationStatus,             \* Status of notification sending
    validTaskIDs                    \* Set of valid task IDs in the system

vars == <<taskCompletionOperationStatus, displayedFeedback, notificationStatus, validTaskIDs>>

\* TYPE INVARIANT
TypeOK ==
    /\ taskCompletionOperationStatus \in {"pending", "success", "failure"}
    /\ displayedFeedback \in {"none"} \cup 
        {"✓ Task marked as done: " \o ToString(id) \o ". " \o desc : id \in TaskIDs, desc \in TaskDescriptions} \cup
        {"❌ Error: Task not found"} \cup
        {"📧 Notification sent"}
    /\ notificationStatus \in {"not_sent", "sent", "failed"}
    /\ validTaskIDs \subseteq TaskIDs

\* INITIAL STATE
Init ==
    /\ taskCompletionOperationStatus = "pending"
    /\ displayedFeedback = "none"
    /\ notificationStatus = "not_sent"
    /\ validTaskIDs \in SUBSET TaskIDs  \* Arbitrary subset of possible task IDs

\* ACTIONS
\* Successful task completion
SuccessfulTaskCompletion(task_id, task_description) ==
    /\ task_id \in validTaskIDs
    /\ taskCompletionOperationStatus = "pending"
    /\ taskCompletionOperationStatus' = "success"
    /\ displayedFeedback' = "✓ Task marked as done: " \o ToString(task_id) \o ". " \o task_description
    /\ UNCHANGED <<notificationStatus, validTaskIDs>>

\* Failed task completion due to invalid task ID
FailedTaskCompletion(task_id) ==
    /\ task_id \notin validTaskIDs
    /\ taskCompletionOperationStatus = "pending"
    /\ taskCompletionOperationStatus' = "failure"
    /\ displayedFeedback' = "❌ Error: Task not found"
    /\ UNCHANGED <<notificationStatus, validTaskIDs>>

\* Successful notification sending after task completion
NotificationSent ==
    /\ taskCompletionOperationStatus = "success"
    /\ notificationStatus = "not_sent"
    /\ notificationStatus' = "sent"
    /\ displayedFeedback' = "📧 Notification sent"
    /\ UNCHANGED <<taskCompletionOperationStatus, validTaskIDs>>

\* Reset system state for next operation
ResetState ==
    /\ taskCompletionOperationStatus' = "pending"
    /\ displayedFeedback' = "none"
    /\ notificationStatus' = "not_sent"
    /\ UNCHANGED validTaskIDs

\* Next-state relation
Next ==
    \/ \E task_id \in TaskIDs, task_description \in TaskDescriptions:
         SuccessfulTaskCompletion(task_id, task_description)
    \/ \E task_id \in TaskIDs: FailedTaskCompletion(task_id)
    \/ NotificationSent
    \/ ResetState

\* SPECIFICATION
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* INVARIANTS
\* Feedback must be shown immediately after task completion operation
ImmediateFeedbackInvariant ==
    (taskCompletionOperationStatus \in {"success", "failure"}) => (displayedFeedback # "none")

\* Notification confirmation appears only after notification is sent
NotificationFeedbackInvariant ==
    (displayedFeedback = "📧 Notification sent") => (notificationStatus = "sent")

\* Success message is shown only for successful task completions
SuccessFeedbackInvariant ==
    \E id \in TaskIDs, desc \in TaskDescriptions:
        (displayedFeedback = "✓ Task marked as done: " \o ToString(id) \o ". " \o desc) =>
            (taskCompletionOperationStatus = "success")

\* Error message is shown only for failed task completions
ErrorFeedbackInvariant ==
    (displayedFeedback = "❌ Error: Task not found") =>
        (taskCompletionOperationStatus = "failure")

\* PROPERTIES
\* Eventually all pending operations will complete and provide feedback
EventualFeedback ==
    [](taskCompletionOperationStatus = "pending" => 
       <>(taskCompletionOperationStatus # "pending" /\ displayedFeedback # "none"))

\* Every successful task completion is eventually followed by a notification confirmation
EventualNotification ==
    [](taskCompletionOperationStatus = "success" => <>(displayedFeedback = "📧 Notification sent"))

\* System always returns to ready state
EventualReset ==
    []<>(taskCompletionOperationStatus = "pending" /\ displayedFeedback = "none")

\* THEOREMS
THEOREM FeedbackCorrectness ==
    Spec => [](ImmediateFeedbackInvariant /\ NotificationFeedbackInvariant /\ 
              SuccessFeedbackInvariant /\ ErrorFeedbackInvariant)

THEOREM FeedbackLiveness ==
    Spec => (EventualFeedback /\ EventualNotification /\ EventualReset)

=============================================================================
\* Modification History
\* Created by Law Generator Agent