;;; TAKU -- the Takeuchi function, uncurried: its arguments a tuple.
;;;
;;; From OCaml's classic test programs (testsuite/tests/misc/taku.ml, ocaml
;;; commit 7da997d28b1a), ported to FX-26. The original sums 200 runs of
;;; tak(18,12,6) and prints 1400; that takes milliseconds, so the port
;;; sums `iterations` = 1000 runs. Answer: 7000 (= 1400 * 5, since
;;; each run is 7); with `iterations` 200 it is the reference's 1400.
;;; The tuple is a product, `(productof (x int) (y int) (z int))`, made at
;;; each call and taken apart by `extract`, as the source says (ocamlopt
;;; itself passes such a tuple in registers; FX-26's compilers may not).

(define-type triple (productof (x int) (y int) (z int)))

(define* tak (subr spin (triple) int)
  (lambda (t)
    (let ((x (extract t x)) (y (extract t y)) (z (extract t z)))
      (if (> x y)
          (tak (product (x (tak (product (x (- x 1)) (y y) (z z))))
                        (y (tak (product (x (- y 1)) (y z) (z x))))
                        (z (tak (product (x (- z 1)) (y x) (z y))))))
          z))))

;; The inputs, where no compiler can fold them: globals.
(define input1 int 18)
(define input2 int 12)
(define input3 int 6)
(define iterations int 1000)

(define* repeat (subr spin (int) int)
  (lambda (n)
    (if (<= n 0)
        0
        (+ (tak (product (x input1) (y input2) (z input3))) (repeat (- n 1))))))
(repeat iterations)
