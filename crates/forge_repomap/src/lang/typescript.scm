;; TypeScript specific queries
;; Includes all JavaScript queries plus:

;; Interfaces
(interface_declaration
  name: (type_identifier) @interface)

;; Type aliases
(type_alias_declaration
  name: (type_identifier) @type)

;; Enums
(enum_declaration
  name: (identifier) @enum)

;; Generic type parameters
(type_parameter_declaration
  name: (type_identifier) @type)

;; Class properties with type annotations
(public_field_definition
  name: (property_identifier) @variable
  type: (_))

;; Method signatures in interfaces
(method_signature
  name: (property_identifier) @method)