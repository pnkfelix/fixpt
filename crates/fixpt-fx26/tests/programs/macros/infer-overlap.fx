;; ! a `union`'s members must be told apart by their shapes in the source
;; Clauses whose patterns may match one use: a signature's `union` tells
;; its members apart by their shapes, as `syntax-rules`' order does not.
(define-syntax m
  (syntax-rules ()
    ((_ (a b)) (+ a b))
    ((_ e) e)))
(m (1 2))
