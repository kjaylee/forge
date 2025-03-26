------------------------------ MODULE CommandInputProcessing ------------------------------
(***************************************************************************)
(* TLA+ Specification for REQ-EVENT-001: Process Command Input              *)
(* This module formalizes how the system accepts and parses the             *)
(* "todo done [task_id]" command from the command line interface.           *)
(***************************************************************************)

EXTENDS Integers, Sequences, TLC

(***************************************************************************)
(* Constants                                                                *)
(***************************************************************************)
CONSTANTS 
    \* Valid command prefix for marking a task as done
    VALID_COMMAND_PREFIX,
    \* Set of possible task IDs (natural numbers)
    TASK_ID_SET,
    \* Set of possible messages the system can return
    POSSIBLE_MESSAGES

(***************************************************************************)
(* Variables                                                                *)
(***************************************************************************)
VARIABLES
    \* The current input command (a string)
    command,
    \* The extracted task ID if valid, otherwise NULL
    extractedTaskId,
    \* System message after processing (success or error)
    systemMessage,
    \* Current parsing state: one of {"initial", "parsing", "completed", "error"}
    parserState

\* Variable group for easier reference in temporal formulas
vars == <<command, extractedTaskId, systemMessage, parserState>>

(***************************************************************************)
(* Type Invariant                                                           *)
(***************************************************************************)
TypeOK ==
    /\ command \in STRING
    /\ extractedTaskId \in TASK_ID_SET \union {NULL}
    /\ systemMessage \in POSSIBLE_MESSAGES
    /\ parserState \in {"initial", "parsing", "completed", "error"}

(***************************************************************************)
(* Helper Functions                                                         *)
(***************************************************************************)

\* Function to check if a string starts with a given prefix
StartsWithPrefix(str, prefix) ==
    LET strLen == Len(str)
        prefixLen == Len(prefix)
    IN
        /\ strLen >= prefixLen
        /\ SubSeq(str, 1, prefixLen) = prefix

\* Function to extract and validate the task ID from a command
ExtractTaskId(cmd) ==
    LET 
        prefixLen == Len(VALID_COMMAND_PREFIX) + 1 \* +1 for the space
        remainingText == SubSeq(cmd, prefixLen, Len(cmd))
    IN
        IF /\ Len(cmd) > prefixLen
           /\ StartsWithPrefix(cmd, VALID_COMMAND_PREFIX)
           /\ remainingText \in TASK_ID_SET
        THEN remainingText
        ELSE NULL

(***************************************************************************)
(* Initial State                                                            *)
(***************************************************************************)
Init ==
    /\ command = ""
    /\ extractedTaskId = NULL
    /\ systemMessage = "Ready"
    /\ parserState = "initial"

(***************************************************************************)
(* State Transitions                                                        *)
(***************************************************************************)

\* Receive a command input from the user
ReceiveCommand(cmd) ==
    /\ parserState = "initial"
    /\ command' = cmd
    /\ parserState' = "parsing"
    /\ UNCHANGED <<extractedTaskId, systemMessage>>

\* Parse the received command
ParseCommand ==
    /\ parserState = "parsing"
    /\ LET taskId == ExtractTaskId(command)
       IN
          IF taskId # NULL THEN
              \* Valid command format with a parseable task ID
              /\ extractedTaskId' = taskId
              /\ systemMessage' = "Command parsed successfully"
              /\ parserState' = "completed"
          ELSE
              \* Invalid command format
              /\ extractedTaskId' = NULL
              /\ systemMessage' = "Invalid command format"
              /\ parserState' = "error"
    /\ UNCHANGED command

\* Reset the system for next command
Reset ==
    /\ parserState \in {"completed", "error"}
    /\ command' = ""
    /\ extractedTaskId' = NULL
    /\ systemMessage' = "Ready"
    /\ parserState' = "initial"

\* Next state relation combining all possible transitions
Next ==
    \/ \E cmd \in STRING : ReceiveCommand(cmd)
    \/ ParseCommand
    \/ Reset

(***************************************************************************)
(* Temporal Formula and Specification                                       *)
(***************************************************************************)

\* The complete system specification
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety Properties                                                        *)
(***************************************************************************)

\* The system never extracts an invalid task ID
ValidTaskIdExtraction ==
    [](extractedTaskId # NULL => extractedTaskId \in TASK_ID_SET)

\* Command input doesn't change system state until fully parsed
NoStateChangeUntilParsed ==
    []((parserState = "initial" /\ command' # command) => 
        (extractedTaskId' = extractedTaskId /\ parserState' = "parsing"))

\* When a valid command is recognized, it must be properly parsed
ValidCommandProperlyParsed ==
    []((parserState = "parsing" /\ StartsWithPrefix(command, VALID_COMMAND_PREFIX) /\ 
        ExtractTaskId(command) # NULL) => 
        <>(extractedTaskId = ExtractTaskId(command) /\ parserState = "completed"))

\* When an invalid command is recognized, it must result in an error
InvalidCommandRejected ==
    []((parserState = "parsing" /\ 
        (\/ ~StartsWithPrefix(command, VALID_COMMAND_PREFIX)
         \/ ExtractTaskId(command) = NULL)) => 
        <>(parserState = "error"))

(***************************************************************************)
(* Liveness Properties                                                      *)
(***************************************************************************)

\* The system eventually processes any received command
EventualCommandProcessing ==
    [](parserState = "parsing" => <>(parserState \in {"completed", "error"}))

\* The system eventually resets after processing a command
EventualReset ==
    []((parserState \in {"completed", "error"}) => <>(parserState = "initial"))

(***************************************************************************)
(* Invariants to be checked                                                 *)
(***************************************************************************)
THEOREM Spec => []TypeOK
THEOREM Spec => ValidTaskIdExtraction
THEOREM Spec => NoStateChangeUntilParsed
THEOREM Spec => EventualCommandProcessing
THEOREM Spec => EventualReset

=============================================================================
\* Modification History
\* Created: TLA+ specification for REQ-EVENT-001 (Process Command Input)
\* Traceability: Implements requirement REQ-EVENT-001