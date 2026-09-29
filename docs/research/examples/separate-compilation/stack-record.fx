;;; A "module" as a value, in FX-26 today: a product of procedures.
;;; Two files, joined as the front end joins its files today.

;;; ---- stack.fx : the interface (a type) and one implementation ----
(define-type (stack-ops (s type))
  (productof (empty s)
             (push (subr pure (int s) s))
             (top  (subr pure (s) int))))

(define list-stack (stack-ops (listof int acyclic))
  (product (empty nil)
           (push (lambda (x s) (cons x s)))
           (top  (lambda (s) (if (null? s) 0 (car s))))))

;;; ---- client.fx : written for any s, so it cannot see the list ----
(define use-stack (poly ((s type)) (subr pure ((stack-ops s)) int))
  (plambda ((s type))
    (lambda (m) ((extract m top) ((extract m push) 2 ((extract m push) 1 (extract m empty)))))))

(use-stack list-stack)                    ; 2
