;; ! its expansion defines `helper`, which its contract does not say a use defines, nor is it its own
;; A name the transformer writes, not renamed: the program's, which nothing
;; says the use defines.
(define-syntax define-const
  (macro (_ p1 @ bvar expr) (defn p1))
  (er-macro-transformer
    (lambda (form rename compare)
      `(,(rename 'begin) (,(rename 'define) helper int 1)
                         (,(rename 'define) ,(car (cdr form)) int ,(car (cdr (cdr form))))))))
(define-const seven 7)
