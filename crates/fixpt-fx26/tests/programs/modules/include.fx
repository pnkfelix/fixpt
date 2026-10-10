;; => 125
;; `(include m)` (`TODO.md` §69): `m`'s values the module's own, in one
;; bucket with its definitions, seen by all of them: a constant (`z`), a
;; `define-rec` and a lambda use them, `include`s anywhere among the items.
(define a (module (define x int 1) (define double (subr pure (int) int) (lambda (n) (* 2 n)))))
(define b (module (define y int 20)))
(define m
  (module
    (include a)
    (define z int (+ x y))
    (define-rec
      (ev? (subr spin (int) bool) (lambda (n) (if (= n 0) #t (od? (- n 1)))))
      (od? (subr spin (int) bool) (lambda (n) (if (= n 0) #f (ev? (- n 1))))))
    (define quad (subr pure (int) int) (lambda (n) (double (double n))))
    (include b)))
(+ (with m z) (+ (with m (quad x)) (if (with m (ev? y)) 100 0)))
