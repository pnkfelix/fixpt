;; => 8
;; Clauses whose patterns may match one use: no `oneof` tells them apart,
;; but a signature of a member per clause, `(clauses ((expr expr)) (expr))`,
;; inferred, takes them, a use governed by the first clause it matches, as
;; `syntax-rules`' order does (`typed-macros.md`, "Decided: a signature per
;; clause, chosen as the clauses are").
(define-syntax m
  (syntax-rules ()
    ((_ (a b)) (+ a b))
    ((_ e) e)))
(+ (m (1 2)) (m 5))
