;; => 22
;; Reversed: what the transformer gives is closed in the use's environment,
;; and each name it means as the macro's it closes in the macro's.
(define-syntax twice
  (rsc-macro-transformer
    (lambda (form env)
      (let ((r (the (subr pure (datum) datum) (lambda (s) (make-syntactic-closure env '() s))))
            (e (car (cdr form))))
        `(,(r 'let) ((,(r 'x) ,e)) (,(r '+) ,(r 'x) ,(r 'x)))))))
(let ((x 10)) (twice (+ x 1)))
