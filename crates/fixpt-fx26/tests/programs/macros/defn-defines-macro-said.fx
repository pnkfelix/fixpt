;; => 15
;; What a use defines, said in what its signature makes: here a macro, of
;; the signature written (`(ℓ (syntax σ))`), which its expansion is held to.
(define-syntax def-adder
  (macro (bvar (many expr)) (defn (A (macro (expr) expr))))
  (syntax-rules
    ((_ name k) (define-syntax name (syntax-rules ((_ e) (+ e k)))))))
(def-adder add5 5)
(add5 10)
