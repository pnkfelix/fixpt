;; ! its contract says a use defines `seven`, and its expansion does not
;; A name the contract says a use defines, not defined.
(define-syntax define-const
  (macro (bvar expr) (defn (A var)))
  (er-macro-transformer
    (lambda (form rename compare)
      `(,(rename 'define) ,(rename 'seven) int ,(car (cdr (cdr form)))))))
(define-const seven 7)
