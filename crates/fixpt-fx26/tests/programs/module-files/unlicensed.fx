;; The same, but its entry point also touches a region of its own choosing,
;; `@user`, which a program it is run beside may name: refused.
(module-parameters ((r region)))
(define count (ref int r) (new 0))
(define shared (ref int @user) (new 0))
(define feed (subr (maxeff (read r) (write r) (write @user)) (int) int)
  (lambda (n) (begin (set shared n) (set count (+ (get count) n)) (get count))))
