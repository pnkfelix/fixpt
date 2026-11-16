;; ! a use of `def-five`: its signature says it defines `five`, a macro of `(macro (_) expr)`, and its expansion does not
;; A value defined where a macro is said.
(define-syntax def-five
  (macro (_ name @ bvar) (defn (name (macro (_) expr))))
  (syntax-rules
    ((_ name) (define name 5))))
(def-five five)
