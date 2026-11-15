;; ! its expansion depends on how its use's bound names are spelled
;; Its expression placed in the scope of the name defined first, which its
;; contract does not put it in: a use whose expression names a global of
;; that spelling reads the definition's.
(define-syntax define-pair
  (macro (bvar bvar expr) (defn (A var) (AD var)))
  (er-macro-transformer
    (lambda (form rename compare)
      (let ((a (car (cdr form))) (b (car (cdr (cdr form)))) (e (car (cdr (cdr (cdr form))))))
        `(,(rename 'begin) (,(rename 'define) ,a int 1)
                           (,(rename 'define) ,b int ,e))))))
(define x int 100)
(define-pair x y (+ x 1))
