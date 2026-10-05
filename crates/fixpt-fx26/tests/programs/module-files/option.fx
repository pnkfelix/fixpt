;; A datatype with a parameter, in a module's file: `(define-type (option
;; (a type)) …)`, as it expands, is `(define-type option (dlambda ((a type))
;; …))`, and the constructors are polymorphic.
(define-datatype (option (a type)) (none) (some a))
(define seven (option int) (some 7))
