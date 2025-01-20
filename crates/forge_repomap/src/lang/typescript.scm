;; Functions and Methods
(function_declaration
  name: (identifier) @function)

(method_definition
  name: (property_identifier) @method)

(arrow_function
  parameter: (identifier) @parameter)

;; Classes and Interfaces
(class_declaration
  name: (identifier) @class)

[
  (interface_declaration
    name: (type_identifier) @interface.name)
  (type_alias_declaration
    name: (type_identifier) @type.alias)
] @type.declaration

;; Variables and Constants
(variable_declarator
  name: (identifier) @variable)

((identifier) @constant
  (#match? @constant "^[A-Z][A-Z_]*$"))

;; TypeScript specific nodes
(property_signature
  name: (property_identifier) @property)

(method_signature
  name: (property_identifier) @method_signature)

(enum_declaration
  name: (identifier) @enum)

;; Type Parameters
(type_parameter
  name: (type_identifier) @type_parameter)

;; Export/Import
(export_statement
  declaration: (_) @exported_declaration)

(import_statement
  source: (_) @import_source)