;;; Closures made in a region with `rlambda`: a `letrec`'s helpers, and a
;;; closure per element, each called there; a polymorphic one too, a
;;; `plambda` whose body is an `rlambda`, since making a closure is the only
;;; effect it has. Calling a closure made in `r` reads `r`, so the list of
;;; them is kept at a region of its own, `l`, in the same arena: kept where
;;; they read, they could have fetched each other, and would have to say
;;; `spin`.
(define-type (closures (r region) (l region)) (listof (subr (read r) (int) int) l))
(define adders (subr spin (int) int)
  (lambda (n)
    (letrena r
      (letregion l
        (letrec ((make (subr (maxeff (alloc r) (alloc l) (read r) spin)
                             (int (closures r l))
                             (closures r l))
                   (rlambda r (i acc)
                     (if (= i 0) acc (make (- i 1) (rcons r (rlambda r ((x int)) (+ x i)) acc)))))
                 (apply-all (subr (maxeff (read r) (read l) spin) ((closures r l) int) int)
                   (rlambda r (fs acc) (if (null? fs) acc (apply-all (cdr fs) ((car fs) acc))))))
          (apply-all (make n nil) 0))))))

(define twice (subr pure (int) int)
  (lambda (n)
    (letrena r
      (let ((id (the (poly ((t type)) (subr (read r) (t) t))
                     (plambda ((t type)) (rlambda r ((x t)) x)))))
        (+ ((proj id int) n) ((proj id int) n))))))

;; cons-chain: the list is in @l
(the (listof int @l) (cons (adders 10) (cons (twice 21) nil)))
