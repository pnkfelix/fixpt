;;; Closures made in a region with `rlambda`: a `letrec`'s helpers, and a
;;; closure per element, each called there; a polymorphic one too, a
;;; `plambda` whose body is an `rlambda`, since making a closure is the only
;;; effect it has.
(define adders (subr pure (int) int)
  (lambda (n)
    (letrena r
      (letrec ((make (subr (maxeff (alloc r) (read r)) (int (listof (subr (read r) (int) int) r)) (listof (subr (read r) (int) int) r))
                 (rlambda r (i acc)
                   (if (= i 0) acc (make (- i 1) (rcons r (rlambda r ((x int)) (+ x i)) acc)))))
               (apply-all (subr (read r) ((listof (subr (read r) (int) int) r) int) int)
                 (rlambda r (fs acc) (if (null? fs) acc (apply-all (cdr fs) ((car fs) acc))))))
        (apply-all (make n nil) 0)))))

(define twice (subr pure (int) int)
  (lambda (n)
    (letrena r
      (let ((id (the (poly ((t type)) (subr (read r) (t) t)) (plambda ((t type)) (rlambda r ((x t)) x)))))
        (+ ((proj id int) n) ((proj id int) n))))))

(the (listof int @l) (cons (adders 10) (cons (twice 21) nil)))
