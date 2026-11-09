;; => (22 101)
;; The same, by syntactic closures: what the transformer gives is closed in
;; the macro's environment, and the operand it closes in the use's.
(define helper (subr pure (int) int) (lambda (x) (+ x 1)))
(define-syntax twice
  (sc-macro-transformer
    (lambda (form env)
      (let ((e (make-syntactic-closure env '() (car (cdr form)))))
        `(let ((x ,e)) (+ x x))))))
(define-syntax inc
  (sc-macro-transformer
    (lambda (form env) `(helper ,(make-syntactic-closure env '() (car (cdr form)))))))
(list (let ((x 10)) (twice (+ x 1))) (let ((helper 100)) (inc helper)))
