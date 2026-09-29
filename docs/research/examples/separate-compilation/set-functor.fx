;;; A functor, in FX-26 today: a polymorphic procedure from a product of
;;; procedures (the argument structure) to another (the result).

;;; ---- set.fx : the argument's interface, the result's, and the functor ----
(define-type (eq-ops (t type)) (productof (eq (subr pure (t t) bool))))
(define-type (set-ops (t type))
  (productof (empty  (listof t acyclic))
             (insert (subr pure (t (listof t acyclic)) (listof t acyclic)))
             (member (subr pure (t (listof t acyclic)) bool))))

(define make-set (poly ((t type)) (subr pure ((eq-ops t)) (set-ops t)))
  (plambda ((t type))
    (lambda (e)
      (product
        (empty nil)
        (insert (lambda (x s) (cons x s)))
        (member (letrec ((mem (subr pure (t (listof t acyclic)) bool)
                           (lambda (x s)
                             (if (null? s) #f
                                 (if ((extract e eq) x (car s)) #t (mem x (cdr s)))))))
                  mem))))))

;;; ---- client.fx : applies the functor, then uses the result ----
(define int-set (set-ops int) (make-set (product (eq (lambda (a b) (= a b))))))
(define* has-two (subr pure () bool)
  (lambda ()
    ((extract int-set member) 2
      ((extract int-set insert) 2 ((extract int-set insert) 1 (extract int-set empty))))))
(has-two)                                 ; #t
