;; ! its contract says a use defines `seven`, and its expansion does not
;; A name the contract says a use defines, not defined.
(define-syntax define-const
  (macro (_ p1 @ bvar expr) (defn p1))
  (er-macro-transformer
    (lambda (form rename compare)
      `(,(rename 'define) ,(rename 'seven) int ,(car (cdr (cdr form)))))))
(define-const seven 7)
