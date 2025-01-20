;; Functions
(function_item
  name: (identifier) @function)

;; Methods in impls
(impl_item 
  body: (declaration_list 
    (function_item
      name: (identifier) @method)))

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
(impl_item 
  trait: (type_identifier)? @impl_trait
  type: (type_identifier) @impl_type)

;; Type aliases
(type_item
  name: (type_identifier) @type)

;; Constants
(const_item
  name: (identifier) @constant)

;; Static items
(static_item
  name: (identifier) @static)

;; Modules
(mod_item
  name: (identifier) @module)