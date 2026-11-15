;; ! a use of `def-adder`: its signature says `add5` is a macro of `(macro (expr) expr)`, and its expansion defines one of another signature
;; A macro defined of another signature than the one said.
(define-syntax def-adder
  (macro (bvar (many expr)) (defn (A (macro (expr) expr))))
  (syntax-rules
    ((_ name k) (define-syntax name (syntax-rules ((_ e f) (+ e (+ f k))))))))
(def-adder add5 5)
