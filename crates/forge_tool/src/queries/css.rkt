;; Capture selectors and their nested selectors
(rule_set
    (selectors
        (class_selector) @name.definition.class
    )
) @definition.rule

;; Capture @media queries
(media_statement
    (feature_name) @name.definition.media
) @definition.media

;; Capture @keyframes
(keyframes_statement
    name: (identifier) @name.definition.keyframes
) @definition.keyframes

;; Capture custom properties
(custom_property_declaration
    name: (property_name) @name.definition.property
) @definition.property

;; Capture variables
(declaration
    name: (property_name) @name
    value: (plain_value) @value
    (#match? @name "^--")
) @definition.variable