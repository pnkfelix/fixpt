;; ! a procedure kept in `@heap` reads `@heap`, so it could reach itself
;; A procedure given to an abstract type constructor may be kept anywhere
;; its unseen representation keeps it: one that reads must say `spin`.
(define-type stack-sig
  (moduleof (abs stack (=> (type) type))
            (val empty (poly ((a type)) (stack a)))
            (val is-empty (poly ((a type)) (subr (read @heap) ((stack a)) bool)))
            (val push (poly ((a type)) (subr (alloc @heap) (a (stack a)) (stack a))))
            (val top (poly ((a type)) (subr (read @heap) ((stack a)) a)))
            (val pop (poly ((a type)) (subr (read @heap) ((stack a)) (stack a))))))
(define list-stack stack-sig
  (module
    (define-generative (stack (a type)) (listof a @heap))
    (define empty (poly ((a type)) (stack a)) (plambda ((a type)) (up-stack nil)))
    (define is-empty (poly ((a type)) (subr (read @heap) ((stack a)) bool))
      (plambda ((a type)) (lambda (s) (null? (down-stack s)))))
    (define push (poly ((a type)) (subr (alloc @heap) (a (stack a)) (stack a)))
      (plambda ((a type)) (lambda (x s) (up-stack (cons x (down-stack s))))))
    (define top (poly ((a type)) (subr (read @heap) ((stack a)) a))
      (plambda ((a type)) (lambda (s) (car (down-stack s)))))
    (define pop (poly ((a type)) (subr (read @heap) ((stack a)) (stack a)))
      (plambda ((a type)) (lambda (s) (up-stack (cdr (down-stack s))))))))
;; One `push`, at ints and at booleans; a stack's type nameable outside.
(define l (list 1))
(define keep (with list-stack (push (lambda () (car l)) (proj empty (subr (read @heap) () int)))))
