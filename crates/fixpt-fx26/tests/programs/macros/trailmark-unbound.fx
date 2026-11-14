;; ! `hi` names no trailmark here: `(define-syntax hi (trailmark))`
;; A `syntax-rules`' trailmarks are bound where the macro is defined.
(define-syntax foo (syntax-rules #:trailmarks (hi) ((_ hi) 1)))
1
