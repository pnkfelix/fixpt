;; ! `(literal hi)` is a kernel form's word; a name a macro's pattern matches is a trailmark's, `(trailmark hi)`
;; `(literal name)` is for the kernel's forms' words, matched by name.
(define-syntax hi (trailmark))
(define-syntax foo ((literal hi)) (syntax-rules #:trailmarks (hi) ((_ hi) 1)))
1
