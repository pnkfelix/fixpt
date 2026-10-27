;; A program.
(define h (load-module "helper.fx"))
(define* count (subr spin (int int) int)
  (lambda (n k)
    (if (= n 0)
        k
        (count (- n 1) ((with h twice) k)))))
(count 3 1)
