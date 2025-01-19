;; Functions
(function_item
  name: (identifier) @function)

;; Methods
(impl_item
  name: (identifier) @method)

;; Structs
(struct_item
  name: (type_identifier) @struct)

;; Enums
(enum_item
  name: (type_identifier) @enum)

;; Traits
(trait_item
  name: (type_identifier) @trait)

;; Implementations
(impl_item) @implementation

;; Type aliases
(type_item
  name: (type_identifier)) @type

;; Constants
(const_item
  name: (identifier) @constant)

;; Static items
(static_item
  name: (identifier) @constant)

;; Modules
(mod_item
  name: (identifier) @module)