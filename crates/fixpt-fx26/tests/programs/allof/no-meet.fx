;; ! this call fits a (subr spin (int) string) and a (subr spin (int) bool), whose results
;; Both members fit an `int`, and no value is a `string` and a `bool`.
(define f (allof (subr spin (int) string) (subr spin (int) bool))
  (lambda (x) (letrec ((loop (subr spin (int) void) (lambda (n) (loop n)))) (loop x))))
(f 1)
