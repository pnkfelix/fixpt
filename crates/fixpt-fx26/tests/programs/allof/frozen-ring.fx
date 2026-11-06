;; => (1 1)
;; Frozen data that is cyclic, at `const`: built and written in a
;; `letfreeze`'s region, which is masked, then frozen. No one writes it
;; after, so both views read the one ring.
;; `ab` and `ac` share the tag `a`: `(sum a 1)` is both.
(define-type ab (sumof (a int) (b int)))
(define-type ac (sumof (a int) (c int)))
(define ring2 (poly ((t type)) (subr pure (t) (listof t const)))
  (plambda ((t type))
    (lambda (x)
      (letfreeze r
        (let ((ys (the (listof t r) (list x x))))
          (begin (set-cdr! (cdr ys) ys) ys))))))
(define mk (allof (subr (read (globals ring2)) (ab) (subr pure () (listof ab const)))
                  (subr (read (globals ring2)) (ac) (subr pure () (listof ac const))))
  (lambda (x) (let ((ring (ring2 x))) (lambda () ring))))
(define g (mk (sum a 1)))
(define as-ab (subr pure () (listof ab const)) g)
(define as-ac (subr pure () (listof ac const)) g)
(list (tagcase (car (cdr (cdr (as-ab)))) (a i i) (b j j)) (tagcase (car (as-ac)) (a i i) (c k k)))
