;; ! its expansion places `x` where its contract does not put it in `x`'s scope
;; A transformer that places the body outside the binder its contract says
;; it is in the scope of: the body's `x` would be the global's, 100. Its
;; renamed run leaves the fresh name free.
(define-syntax let1
  (macro (_ (p1 @ bvar expr) p2 @ expr) expr (bind p1 in p2))
  (er-macro-transformer
    (lambda (form rename compare)
      (let ((xe (car (cdr form))) (body (car (cdr (cdr form)))))
        `(,(rename 'begin) (,(rename 'let) ((,(car xe) ,(car (cdr xe)))) 0) ,body)))))
(define x int 100)
(let1 (x 3) (+ x 4))
