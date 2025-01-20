;; Functions
(function_declaration
  name: (identifier) @function)

;; Arrow Functions
(variable_declarator
  name: (identifier) @function
  value: (arrow_function))

;; Methods
(method_definition
  name: (property_identifier) @method)

;; Classes
(class_declaration
  name: (identifier) @class)

;; Variables
(variable_declarator
  name: (identifier) @variable)

;; Constants
((identifier) @constant
 (#match? @constant "^[A-Z][A-Z_]*$"))

;; Object Properties
(pair
  key: (property_identifier) @property)

;; Exports
(export_statement
  declaration: (_) @export)