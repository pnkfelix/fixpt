(define id (subr pure (int) int) (lambda (x) x))
,native id 7
(define fib (subr spin (int) int) (lambda (n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))))
,native fib 30
(define twice (subr pure ((subr pure (int) int) int) int) (lambda (f x) (f (f x))))
,native twice
(define call-c (subr pure ((subr (conv cellular) pure (int) int)) int) (lambda (f) (f 1)))
(fib 25)
(twice (lambda ((x int)) (+ x 5)) 32)
(lambda ((x int)) x)
,native ((lambda ((x int)) (+ x 1)) 41)
