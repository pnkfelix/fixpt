;; => 3
;; A use whose body quotes its binder's name: renamed, the use's references
;; to the binder are, and what it quotes is not, so the expansion is held
;; to a use α-equivalent to it.
(define-syntax let1
  (-> ((bvar expr) (import expr (rho (AA var)))) expr)
  (er-macro-transformer
    (lambda (form rename compare)
      (let ((xe (car (cdr form))) (body (car (cdr (cdr form)))))
        `(,(rename 'let) ((,(car xe) ,(car (cdr xe)))) ,body)))))
(let1 (x 3) (begin 'x x))
