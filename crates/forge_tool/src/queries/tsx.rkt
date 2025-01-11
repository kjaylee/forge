;; Include all TypeScript patterns
(interface_declaration
    name: (type_identifier) @name.definition.interface
) @definition.interface

(type_alias_declaration
    name: (type_identifier) @name.definition.type
) @definition.type

;; Capture React Components (Function and Class based)
(
    [
        (function_declaration
            name: (identifier) @name)
        (variable_declarator
            name: (identifier) @name
            value: [(arrow_function) (function_expression)])
    ] @definition.component
    (#match? @name "^[A-Z]")  ;; React components start with capital letter
)

;; Capture React Class Components
(
    (class_declaration
        name: (identifier) @name
        superclass: (_)?  ;; Optional extends React.Component
    ) @definition.component
    (#match? @name "^[A-Z]")
)

;; Capture Hooks (functions starting with 'use')
(
    [
        (function_declaration
            name: (identifier) @name)
        (variable_declarator
            name: (identifier) @name
            value: [(arrow_function) (function_expression)])
    ] @definition.hook
    (#match? @name "^use[A-Z]")
)

;; Capture regular functions (not components or hooks)
(
    [
        (function_declaration
            name: (identifier) @name)
        (variable_declarator
            name: (identifier) @name
            value: [(arrow_function) (function_expression)])
    ] @definition.function
    (#not-match? @name "^[A-Z]")
    (#not-match? @name "^use[A-Z]")
)