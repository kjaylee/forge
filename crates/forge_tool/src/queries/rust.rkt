;; Capture struct declarations
(struct_item
  name: (type_identifier) @struct.name
) @definition.struct

;; Capture enum declarations
(enum_item
  name: (type_identifier) @enum.name
) @definition.enum

;; Capture trait declarations
(trait_item
  name: (type_identifier) @trait.name
) @definition.trait

;; Capture implementation blocks
(impl_item
  trait: (type_identifier)? @impl.trait
  type: (type_identifier) @impl.type
) @definition.impl

;; Capture function declarations
(function_item
  name: (identifier) @function.name
) @definition.function

;; Capture module declarations
(mod_item
  name: (identifier) @module.name
) @definition.module