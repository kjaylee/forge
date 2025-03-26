-------------------------------- MODULE REQ_STATE_001 --------------------------------
(* This TLA+ specification formally models REQ-STATE-001: "Mark Task as Complete" 
   for the Todo List application. It models the state transitions and properties
   that must be maintained when a user marks a task as complete. *)

EXTENDS Naturals, Sequences, FiniteSets, TLC

(* 
  Constants: 
  - TASK_IDS: The set of all possible task IDs in the system
  - USER_COMMANDS: The set of possible user commands
*)
CONSTANTS TASK_IDS, USER_COMMANDS

(* Type definitions and assumptions *)
ASSUME TASK_IDS \subseteq Nat
ASSUME USER_COMMANDS = {"todo done"}

(*
  Variables:
  - tasks: A function mapping task IDs to records containing task information
  - messages: Sequence of messages displayed to the user
  - command: Current command being executed by the user
  - commandParam: Parameter provided with the command (task ID)
*)
VARIABLES tasks, messages, command, commandParam

(* Define variable sets for easier reference *)
taskVars == <<tasks>>
uiVars == <<messages>>
inputVars == <<command, commandParam>>
vars == <<tasks, messages, command, commandParam>>

(*
  Task record structure:
  [
    id: Natural number - the unique identifier for a task
    description: String - the task description
    status: String - either "incomplete" or "complete"
  ]
*)

(* Type invariant: ensures all variables maintain correct types *)
TypeOK ==
  /\ tasks \in [TASK_IDS -> [id: TASK_IDS,
                         description: STRING,
                         status: {"incomplete", "complete"}]]
  /\ messages \in Seq(STRING)
  /\ command \in {"", "todo done"} \cup {""}
  /\ commandParam \in TASK_IDS \cup {-1}

(* Define initial state *)
Init ==
  /\ tasks \in [TASK_IDS -> [id: TASK_IDS,
                          description: STRING, 
                          status: {"incomplete"}]]
  /\ messages = << >>
  /\ command = ""
  /\ commandParam = -1

(* Helper predicates *)

(* Task exists in the system *)
TaskExists(taskId) == taskId \in DOMAIN tasks

(* Task is in incomplete state *)
TaskIsIncomplete(taskId) == 
  /\ TaskExists(taskId)
  /\ tasks[taskId].status = "incomplete"

(* Actions *)

(* User enters "todo done [task_id]" command *)
EnterCommand ==
  /\ command = ""
  /\ \E taskId \in TASK_IDS:
      /\ commandParam' = taskId
      /\ command' = "todo done"
  /\ UNCHANGED <<tasks, messages>>

(* The system marks a task as complete *)
MarkTaskComplete ==
  /\ command = "todo done"
  /\ TaskExists(commandParam)
  /\ TaskIsIncomplete(commandParam)
  /\ LET taskId == commandParam
         task == tasks[taskId]
     IN
       /\ tasks' = [tasks EXCEPT ![taskId] = [@ EXCEPT !.status = "complete"]]
       /\ messages' = Append(messages, 
                            "✓ Task marked as done: " \o ToString(taskId) \o ". " 
                            \o tasks[taskId].description)
  /\ command' = ""
  /\ commandParam' = -1

(* Task doesn't exist or is already complete *)
InvalidMarkComplete ==
  /\ command = "todo done"
  /\ \/ ~TaskExists(commandParam)
     \/ ~TaskIsIncomplete(commandParam)
  /\ messages' = Append(messages, "Error: Cannot mark task as complete.")
  /\ command' = ""
  /\ commandParam' = -1
  /\ UNCHANGED tasks

(* System state transitions *)
Next ==
  \/ EnterCommand
  \/ MarkTaskComplete
  \/ InvalidMarkComplete

(* Specify the complete behavior of the system *)
Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

(* Properties to verify *)

(* INVARIANT: Task ID must remain unchanged after marking as complete *)
TaskIdInvariant ==
  \A id \in DOMAIN tasks: tasks[id].id = id

(* INVARIANT: Once a task is complete, it remains complete *)
CompletedTaskStaysComplete ==
  [][
    \A id \in DOMAIN tasks:
      tasks[id].status = "complete" =>
        tasks'[id].status = "complete"
  ]_taskVars

(* INVARIANT: Successful task completion results in a specific message format *)
SuccessMessageFormat ==
  \A i \in 1..Len(messages):
    \E id \in DOMAIN tasks:
      tasks[id].status = "complete" =>
        \E j \in 1..Len(messages):
          messages[j] = "✓ Task marked as done: " \o 
                        ToString(id) \o ". " \o 
                        tasks[id].description

(* THEOREM: All properties are satisfied by the specification *)
THEOREM Spec => 
  /\ []TypeOK
  /\ []TaskIdInvariant
  /\ CompletedTaskStaysComplete
  /\ []SuccessMessageFormat

(* 
  Traceability to requirements:
  - MarkTaskComplete action implements "The system shall change the status of a specified 
    task to "complete" when the user executes the "todo done [task_id]" command with a valid task ID"
  - TaskIdInvariant ensures "Task ID must remain unchanged"
  - CompletedTaskStaysComplete ensures "Task status must not revert to incomplete after being marked complete"
  - SuccessMessageFormat ensures "Success message displays "✓ Task marked as done: [task_id]. [task_description]"
*)

=============================================================================