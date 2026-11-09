;; A file's macros naming its types: `meters`, a name, and a type made of
;; it, each read through this file's module.
(define-type meters int)
(define-syntax as-meters (expr) (syntax-rules () ((_ e) (the meters e))))
(define-syntax as-fun (expr) (syntax-rules () ((_ f) (the (subr pure (meters) meters) f))))
