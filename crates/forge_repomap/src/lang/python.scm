;; Classes
(class_definition
  name: (identifier) @class)

;; Functions
(function_definition
  name: (identifier) @function)

;; Methods
(class_definition
  (block
    (function_definition
      name: (identifier) @method)))

;; Variables
(assignment
  left: (identifier) @variable)

;; Constants
((identifier) @constant
 (#match? @constant "^[A-Z][A-Z_]*$"))

;; Imports
(import_statement
  name: (dotted_name) @module)