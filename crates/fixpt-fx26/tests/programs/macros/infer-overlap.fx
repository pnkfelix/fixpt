;; ! a `oneof`'s members must be told apart by their shapes in the source
;; Clauses whose patterns may match one use: `(m (1 2))` is either. One
;; signature says each use's binding structure whatever clause expands it,
;; and none does here: the first clause takes apart an operand the second
;; calls an `expr` (`typed-macros.md`, "Rejected: a signature per clause").
(define-syntax m
  (syntax-rules
    ((_ (a b)) (+ a b))
    ((_ e) e)))
(+ (m (1 2)) (m 5))
