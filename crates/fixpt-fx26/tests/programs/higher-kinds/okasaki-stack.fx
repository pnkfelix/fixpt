;; => (3 2 1)
;; Okasaki's STACK signature (Purely Functional Data Structures, 2.1), as
;; written: `stack` an abstract type constructor of kind (=> (type) type),
;; one module whose operations are polymorphic in the element type. Its
;; encodings without higher kinds, and what they lack, are
;; `modules/stack-by-poly.fx` and `modules/stack-by-functor.fx`.
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
(define s ((select list-stack stack) int)
  (with list-stack (push 3 (push 2 (push 1 (proj empty int))))))
(with list-stack
  (let ((b (push #t (proj empty bool))))
    (list (top s) (top (pop s)) (if (top b) 1 0))))
