;; ! `(n …)` applies `n`, but what follows names `n`: to name a parameter, write `(n : type)`
(define f (-> ((n int)) int (requires (> n 0))) (lambda (n) n))
