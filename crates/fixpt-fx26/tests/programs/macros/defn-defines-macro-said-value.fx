;; ! a use of `def-five`: its signature says it defines `five`, a macro of `(macro () expr)`, and its expansion does not
;; A value defined where a macro is said.
(define-syntax def-five
  (macro (bvar) (defn (A (macro () expr))))
  (syntax-rules
    ((_ name) (define name 5))))
(def-five five)
