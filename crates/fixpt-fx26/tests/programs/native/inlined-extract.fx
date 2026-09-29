;;; A small procedure with an `extract`, inlined where a later form calls
;;; it: the field comes from the checker's facts of the earlier form, which
;;; the later form's compile no longer has, so the body kept for inlining
;;; has its fields resolved when kept. Else the caller has no register code,
;;; and runs as cellular code, ten times slower.
(define-type pt (productof (x int) (y int)))
(define* e (subr pure (pt) int) (lambda (a) (extract a x)))
(define* lp (subr spin (pt int int) int) (lambda (p i acc) (if (= i 0) acc (lp p (- i 1) (+ acc (e p))))))
(define* go (subr spin (int) int) (lambda (n) (lp (product (x 3) (y 2)) n 0)))
(go 1000)
