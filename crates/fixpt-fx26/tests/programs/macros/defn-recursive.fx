;; => 120
;; `define*` and `(define x T lambda)`: the procedure in its own scope.
(define-syntax define-fact
  (-> (bvar bvar) defn)
  (syntax-rules ()
    ((_ f g)
     (begin (define f (->* (int) int) (lambda ((n int)) (if (= n 0) 1 (* n (f (- n 1))))))
            (define* g (subr spin (int) int)
              (lambda ((n int)) (if (= n 0) 1 (* n (g (- n 1))))))))))
(define-fact fact fact2)
(if (= (fact 5) (fact2 5)) (fact 5) 0)
