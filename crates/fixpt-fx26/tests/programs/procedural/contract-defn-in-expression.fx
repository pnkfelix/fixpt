;; ! `define-const` makes definitions, which are made at the top level, not where an expression is
;; A use of a macro whose contract makes definitions, where an expression is.
(define-syntax define-const
  (macro (bvar expr) (defn (A var)))
  (er-macro-transformer
    (lambda (form rename compare)
      `(,(rename 'define) ,(car (cdr form)) int ,(car (cdr (cdr form)))))))
(+ 1 (define-const seven 7))
