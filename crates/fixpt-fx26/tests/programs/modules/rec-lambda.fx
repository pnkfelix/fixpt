;; ! `k`, in a `define-rec`, is a `lambda`
;; A module's `define-rec` binds only procedures.
(define bad (module (define-rec (k int 3))))
