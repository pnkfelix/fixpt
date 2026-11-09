;; => (22 101)
;; The same, by explicit renaming: each name the transformer means as where
;; the macro is defined, it renames; the operand it leaves as the use wrote it.
(define helper (subr pure (int) int) (lambda (x) (+ x 1)))
(define-syntax twice
  (er-macro-transformer
    (lambda (form rename compare)
      (let ((e (car (cdr form))))
        `(,(rename 'let) ((,(rename 'x) ,e))
           (,(rename '+) ,(rename 'x) ,(rename 'x)))))))
(define-syntax inc
  (er-macro-transformer
    (lambda (form rename compare) `(,(rename 'helper) ,(car (cdr form))))))
(list (let ((x 10)) (twice (+ x 1))) (let ((helper 100)) (inc helper)))
