;; => 3
;; A family the template names, the top level's, whatever the use binds of
;; its name.
(define-type (box (a type)) (listof a))
(define-syntax boxed (expr)
  (syntax-rules ()
    ((_ e) (length (the (box int) e)))))
(define g (poly ((box (=> (type) type))) (subr pure () nat))
  (plambda ((box (=> (type) type))) (lambda () (boxed (list 1 2 3)))))
((proj g (dlambda ((a type)) a)))
