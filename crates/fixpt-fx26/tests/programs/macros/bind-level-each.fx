;; ! for each repetition inside the one before, a `letrec-shape` whose node says `export*`
;; No level for each repetition: `(a ...)` is every one's together, and each inside the one
;; before is a `letrec-shape`'s.
(define-syntax w
  (macro (_ a @ bvar body @ expr) expr (bind a ... in body))
  (syntax-rules ((_ a body) (let ((a 1)) body))))
(w x x)
