;; Functions
(function_item
  name: (identifier) @function.name
  parameters: (parameters) @function.parameters) @function.definition

;; Methods in impl blocks
(impl_item_function
  name: (identifier) @function.name
  parameters: (parameters) @function.parameters) @function.definition

;; Structs
(struct_item
  name: (identifier) @struct.name
  body: (field_declaration_list)? @struct.body) @struct.definition

;; Enums
(enum_item
  name: (identifier) @enum.name
  body: (enum_variant_list)? @enum.body) @enum.definition

;; Traits
(trait_item
  name: (identifier) @trait.name
  body: (declaration_list)? @trait.body) @trait.definition

;; Impl blocks
(impl_item
  trait: (type_identifier)? @impl.trait
  type: (type_identifier) @impl.type) @impl.definition

;; Type aliases
(type_item
  name: (type_identifier) @type.name
  type: (_) @type.value) @type.definition

;; Module definitions
(mod_item
  name: (identifier) @module.name) @module.definition

;; Use declarations
(use_declaration
  path: (scoped_identifier) @use.path) @use.declaration

;; Documentation comments
(line_documentation_comment) @doc.line
(block_documentation_comment) @doc.block

;; Variables and Constants
(let_declaration
  pattern: (identifier) @variable.name
  type: (_)? @variable.type) @variable.definition

(const_item
  name: (identifier) @const.name
  type: (_) @const.type) @const.definition

;; Attributes
(attribute_item) @attribute
(inner_attribute_item) @attribute.inner

;; Function calls
(call_expression
  function: (_) @function.call)

;; Type references
(type_identifier) @type.reference