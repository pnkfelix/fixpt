;; ! `clamp` is defined already: a macro may not take its name
;; A macro may not take a global's name: `clamp` would be the macro as an
;; operator and the value elsewhere.
(define clamp 0)
(define-syntax clamp (expr) (syntax-rules () ((_ e) e)))
(clamp 100)
