;; Functions and Methods
(function_declaration
  name: (identifier) @function)

(method_definition
  name: (property_identifier) @method)

(arrow_function 
  parameter: [(identifier) (formal_parameters)] @parameter)

;; Classes and Interfaces
(class_declaration
  name: (type_identifier) @class)

;; Changed: Using correct TypeScript node types
(interface_declaration 
  name: (type_identifier) @interface)

(type_alias_declaration 
  name: (type_identifier) @type.alias)

;; Variables and Constants
(variable_declarator
  name: (identifier) @variable)

;; Changed: Simplified constant detection
((identifier) @constant
  (#match? @constant "^[A-Z][A-Z_]*$"))

;; Export/Import
(export_statement
  (declaration) @exported_declaration)

(import_statement 
  (string) @import_source)