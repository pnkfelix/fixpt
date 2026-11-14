;; ! a `syntax-rules` has no list of literals: drop the `()`
;; R7RS's empty list of literals: refused, the trailmarks written only
;; where there are some, `#:trailmarks (name …)`.
(define-syntax foo (syntax-rules () ((_) 1)))
1
