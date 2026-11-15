;; => (7 104)
;; A contract on a syntactic-closure transformer: the body closed in the
;; use's environment, the binder as the use wrote it, the rest the macro's.
(define-syntax let1
  (macro ((bvar expr) (import expr (rho (AA var)))) expr)
  (sc-macro-transformer
    (lambda (form env)
      (let ((xe (car (cdr form))) (body (car (cdr (cdr form)))))
        `(let ((,(car xe) ,(make-syntactic-closure env '() (car (cdr xe)))))
           ,(make-syntactic-closure env (list (car xe)) body))))))
(define x int 100)
(list (let1 (y 3) (+ y 4)) (let1 (x (+ x 1)) (+ x 3)))
