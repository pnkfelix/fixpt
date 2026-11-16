;; => 3
;; A use whose body quotes its binder's name: renamed, the use's references
;; to the binder are, and what it quotes is not, so the expansion is held
;; to a use α-equivalent to it.
(define-syntax let1
  (macro (_ (p1 @ bvar expr) p2 @ expr) expr (bind p1 in p2))
  (er-macro-transformer
    (lambda (form rename compare)
      (let ((xe (car (cdr form))) (body (car (cdr (cdr form)))))
        `(,(rename 'let) ((,(car xe) ,(car (cdr xe)))) ,body)))))
(let1 (x 3) (begin 'x x))
