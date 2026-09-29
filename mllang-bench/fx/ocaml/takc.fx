;;; TAKC -- the Takeuchi function, curried.
;;;
;;; From OCaml's classic test programs (testsuite/tests/misc/takc.ml, ocaml
;;; commit 7da997d28b1a), ported to FX-26. The original sums 200 runs of
;;; (tak 18 12 6) and prints 1400; that takes milliseconds, so the port
;;; sums `iterations` = 20000 runs. Answer: 140000 (= 1400 * 100, since
;;; each run is 7); with `iterations` 200 it is the reference's 1400.
;;; FX-26 procedures take all their arguments at once, so "curried" and
;;; "uncurried" (taku) are the same here; the port keeps the OCaml
;;; argument order and `repeat`'s non-tail recursion.

(define* tak (subr spin (int int int) int)
  (lambda (x y z)
    (if (> x y)
        (tak (tak (- x 1) y z) (tak (- y 1) z x) (tak (- z 1) x y))
        z)))

;; The inputs, where no compiler can fold them: globals.
(define input1 int 18)
(define input2 int 12)
(define input3 int 6)
(define iterations int 20000)

(define* repeat (subr spin (int) int)
  (lambda (n)
    (if (<= n 0) 0 (+ (tak input1 input2 input3) (repeat (- n 1))))))
(repeat iterations)
