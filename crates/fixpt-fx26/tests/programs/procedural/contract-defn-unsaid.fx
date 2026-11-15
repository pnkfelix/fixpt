;; ! its expansion defines `seven`, which its contract does not say a use defines
;; A name of the use's defined, which the contract does not say.
(define-syntax define-const
  (-> (bvar expr) defn)
  (er-macro-transformer
    (lambda (form rename compare)
      `(,(rename 'define) ,(car (cdr form)) int ,(car (cdr (cdr form)))))))
(define-const seven 7)
