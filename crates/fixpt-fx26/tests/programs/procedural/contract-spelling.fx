;; ! its expansion depends on how its use's bound names are spelled
;; A transformer that reads its binder's name: a binder spelled `x` gives
;; one expansion, any other another. Renamed, the use expands otherwise.
(define-syntax let1
  ((bvar expr) (import expr (rho (AA var))))
  (er-macro-transformer
    (lambda (form rename compare)
      (let* ((xe (car (cdr form))) (body (car (cdr (cdr form)))) (b (car xe)))
        (if (and (symbol? b) (compare b 'x))
            `(,(rename 'let) ((,(car xe) ,(car (cdr xe)))) 0)
            `(,(rename 'let) ((,(car xe) ,(car (cdr xe)))) ,body))))))
(let1 (x 3) (+ x 4))
