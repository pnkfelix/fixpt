;; ! a use of `define-const`: its expansion: `(+ 1 2)` is not a definition
;; An expansion that is no definition.
(define-syntax define-const
  (macro (bvar expr) (defn (A var)))
  (er-macro-transformer
    (lambda (form rename compare)
      `(,(rename '+) 1 2))))
(define-const seven 7)
