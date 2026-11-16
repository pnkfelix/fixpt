;; => 7
;; A `oneof` whose members refer to the `mu` around them, told apart once
;; that `mu` is read whole: `(expr)` and `(expr . es)`, `es` itself one or
;; more, so never `()`. Checked against `es` taken for `()` while its body
;; was read (the `mu` table's, before `TODO.md` §290), it was refused.
(define-syntax first-of
  (macro (_ . (mu es (union (expr) (expr . es)))) expr)
  (syntax-rules ((_ e) e)))
(first-of 7)
