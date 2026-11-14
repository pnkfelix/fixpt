;; ! fits the signature of clause 1 first, and clause 2 is the one whose pattern it matches
;; A member written broader than its clause's pattern: `(data)` fits `3`,
;; which only the second clause's pattern matches.
(define-syntax foo (clauses (data) (expr))
  (syntax-rules () ((_ 2) "two") ((_ x) x)))
(foo 3)
