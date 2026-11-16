;; ! a macro's binder is written with its signature, `(macro …)`, not `(syntax …)`
;; A macro's binder written as it once was.
(define-syntax def-five
  (macro (_ name @ bvar) (defn (name (syntax (macro (_) expr)))))
  (syntax-rules ((_ name) (define-syntax name (syntax-rules ((_) 5))))))
