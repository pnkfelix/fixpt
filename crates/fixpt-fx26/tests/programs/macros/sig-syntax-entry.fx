;; ! a macro's binder is written with its signature, `(ℓ (macro σ made))`, not `(syntax …)`
;; A macro's binder written as it once was.
(define-syntax def-five
  (macro (bvar) (defn (A (syntax (macro () expr)))))
  (syntax-rules ((_ name) (define-syntax name (syntax-rules ((_) 5))))))
