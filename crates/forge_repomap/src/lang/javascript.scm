;; Functions
(function_declaration
  name: (identifier) @function)

;; Methods
(method_definition
  name: (property_identifier) @method)

;; Classes
(class_declaration
  name: (identifier) @class)

;; Interfaces
(interface_declaration
  name: (type_identifier) @interface)

;; Variables
(variable_declarator
  name: (identifier) @variable)

;; Constants
((identifier) @constant
 (#match? @constant "^[A-Z][A-Z_]*$"))

;; Exports
(export_statement
  declaration: (_) @module)