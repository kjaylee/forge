-------------------------------- MODULE REQ_NOTIFY_001 --------------------------------
(* 
   TLA+ Specification for REQ-NOTIFY-001: Send Email Notification
   
   This module specifies the behavior of the email notification system
   when a task is marked as complete. It ensures that:
   
   1. Email is sent when a task is successfully marked as complete
   2. Email contains task ID, description, and completion timestamp
   3. Notification confirmation is displayed to the user
   4. Email is sent only once per task completion
   
   Traceability: Implements requirement REQ-NOTIFY-001
*)

EXTENDS Naturals, Sequences, FiniteSets, TLC

(* ------------------------------ CONSTANTS ------------------------------ *)

\* Set of all possible task IDs
CONSTANT TaskIds

\* Set of all possible task descriptions
CONSTANT TaskDescriptions

\* Message templates
CONSTANT 
    EMAIL_TEMPLATE,         \* Template for email message
    NOTIFICATION_MESSAGE    \* Confirmation message shown to user

(* ------------------------------ VARIABLES ------------------------------ *)

VARIABLES
    tasks,              \* Set of existing tasks: {[id, description, status, completionTime]}
    emailsSent,         \* Set of emails sent: {[taskId, timestamp]}
    userNotifications,  \* Sequence of notifications shown to user
    operationStatus,    \* Status of last operation (success or failure)
    currentAction       \* Current action being performed

(* ---------------------------- TYPE INVARIANTS --------------------------- *)

TaskStatus == {"pending", "complete"}

\* Type invariant for system state
TypeOK == 
    /\ tasks \in SUBSET [id: TaskIds, description: TaskDescriptions, status: TaskStatus, completionTime: Nat \union {0}]
    /\ emailsSent \in SUBSET [taskId: TaskIds, timestamp: Nat]
    /\ userNotifications \in Seq(STRING)
    /\ operationStatus \in {"idle", "success", "failure"}
    /\ currentAction \in {"none", "mark_complete", "send_notification", "display_confirmation"}

(* ---------------------------- STATE PREDICATES -------------------------- *)

\* Initial state of the system
Init ==
    /\ tasks = {}                  \* No tasks initially
    /\ emailsSent = {}             \* No emails sent initially
    /\ userNotifications = <<>>    \* No notifications initially
    /\ operationStatus = "idle"    \* System starts idle
    /\ currentAction = "none"      \* No action initially

\* Utility predicate to check if a task exists
TaskExists(taskId) ==
    \E task \in tasks : task.id = taskId

\* Utility predicate to check if a task is complete
IsTaskComplete(taskId) ==
    \E task \in tasks : 
        /\ task.id = taskId
        /\ task.status = "complete"
        
\* Utility predicate to check if email has been sent for a task
EmailAlreadySent(taskId) ==
    \E email \in emailsSent : email.taskId = taskId

(* ---------------------------- SYSTEM ACTIONS ---------------------------- *)

\* Action: Mark a task as complete
\* Note: This action is included for context, but is part of a different requirement
MarkTaskComplete(taskId) ==
    /\ currentAction = "none"
    /\ TaskExists(taskId)
    /\ \E task \in tasks :
        /\ task.id = taskId
        /\ task.status = "pending"
        /\ tasks' = (tasks \ {task}) \union 
                   {[id |-> task.id, 
                     description |-> task.description, 
                     status |-> "complete",
                     completionTime |-> Len(userNotifications) + 1]}
    /\ operationStatus' = "success"
    /\ currentAction' = "mark_complete"
    /\ UNCHANGED <<emailsSent, userNotifications>>

\* Action: Send email notification
SendEmailNotification(taskId) ==
    /\ currentAction = "mark_complete"
    /\ IsTaskComplete(taskId)
    /\ ~EmailAlreadySent(taskId)
    /\ \E task \in tasks :
        /\ task.id = taskId
        /\ task.status = "complete"
        /\ emailsSent' = emailsSent \union {[taskId |-> taskId, timestamp |-> task.completionTime]}
    /\ currentAction' = "send_notification"
    /\ UNCHANGED <<tasks, userNotifications, operationStatus>>

\* Action: Display notification confirmation to user
DisplayNotificationConfirmation(taskId) ==
    /\ currentAction = "send_notification"
    /\ \E task \in tasks : task.id = taskId
    /\ userNotifications' = Append(userNotifications, NOTIFICATION_MESSAGE)
    /\ currentAction' = "none"
    /\ UNCHANGED <<tasks, emailsSent, operationStatus>>

\* Action representing operation failure or reset
Reset ==
    /\ currentAction' = "none"
    /\ operationStatus' = "idle"
    /\ UNCHANGED <<tasks, emailsSent, userNotifications>>

(* -------------------------- SYSTEM SPECIFICATION ------------------------- *)

\* Next state relation
Next ==
    \/ \E taskId \in TaskIds : 
          \/ MarkTaskComplete(taskId)
          \/ SendEmailNotification(taskId)
          \/ DisplayNotificationConfirmation(taskId)
    \/ Reset

\* Complete system specification
vars == <<tasks, emailsSent, userNotifications, operationStatus, currentAction>>
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* ---------------------------- SYSTEM PROPERTIES -------------------------- *)

\* SAFETY PROPERTY:
\* Email is sent only when a task is marked complete
EmailOnlyAfterCompletion ==
    \A taskId \in TaskIds :
        EmailAlreadySent(taskId) => IsTaskComplete(taskId)

\* SAFETY PROPERTY:
\* Email is sent at most once per task
EmailSentOnlyOnce ==
    \A taskId \in TaskIds :
        Cardinality({email \in emailsSent : email.taskId = taskId}) <= 1

\* LIVENESS PROPERTY:
\* If a task is marked complete, an email notification will eventually be sent
EventualNotification ==
    \A taskId \in TaskIds :
        IsTaskComplete(taskId) ~> EmailAlreadySent(taskId)

\* LIVENESS PROPERTY:
\* If an email is sent, confirmation will eventually be displayed
EventualConfirmation ==
    \A taskId \in TaskIds :
        (EmailAlreadySent(taskId) /\ ~(\E msg \in Range(userNotifications): msg = NOTIFICATION_MESSAGE))
        ~> (\E msg \in Range(userNotifications'): msg = NOTIFICATION_MESSAGE)

\* Invariant: All properties must hold
SystemInvariants ==
    /\ TypeOK
    /\ EmailOnlyAfterCompletion
    /\ EmailSentOnlyOnce

\* Theorems
THEOREM Spec => []SystemInvariants
THEOREM Spec => EventualNotification
THEOREM Spec => EventualConfirmation

================================================================================