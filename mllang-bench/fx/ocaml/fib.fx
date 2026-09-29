;;; FIB -- the doubly recursive Fibonacci function, fib 0 = fib 1 = 1.
;;;
;;; From OCaml's classic test programs (testsuite/tests/misc/fib.ml, ocaml
;;; commit 7da997d28b1a), ported to FX-26. The original computes fib 30
;;; (its default; a command-line argument may replace it) and prints
;;; 1346269, the reference output; that takes milliseconds, so the port
;;; computes fib `input` = 42. Answer: 433494437 (with `input` 30, the
;;; reference's 1346269).

(define* fib (subr spin (int) int)
  (lambda (n)
    (if (< n 2) 1 (+ (fib (- n 1)) (fib (- n 2))))))

;; The input, where no compiler can fold it: a global.
(define input int 42)
(fib input)
