;; ! a `syntax-rules`' names its patterns match are its trailmarks: `#:trailmarks (else)`
;; R7RS's list of literals: refused, saying how it is written now.
(define-syntax foo (syntax-rules (else) ((_ else) 1)))
1
