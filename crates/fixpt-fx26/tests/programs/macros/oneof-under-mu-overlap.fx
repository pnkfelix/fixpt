;; ! a `oneof`'s members must be told apart by their shapes in the source
;; Members that refer to the `mu` around them, which may be of the same
;; syntax once it is known: `(expr . es)` and `(expr expr . es)`, `es` here
;; not `()`. Checked against `es` taken for `()` while its body was read
;; (the `mu` table's, before `TODO.md` §290), they were told apart.
(define-syntax pairs
  (macro (_ . (mu es (union () (expr . es) (expr expr . es)))) expr)
  (syntax-rules ((_) 0)))
0
