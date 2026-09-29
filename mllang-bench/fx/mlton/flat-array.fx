;;; FLAT-ARRAY -- a fold over a vector of 1000000 pairs, with Int32 overflow
;;; caught by a handler.
;;;
;;; From MLton's benchmark suite (benchmark/tests/flat-array.sml, commit
;;; aa2fd1ad9b91), ported to FX-26. Iteration count (ours; MLton's driver
;;; was not fetched): (doit 10), folding the same vector 10 times.
;;; Answer: 1105694191, the fold's sum (the original checks for it).
;;;
;;; MLton's `int` is 32 bits, and the fold relies on it: `a + b + c handle
;;; Overflow => 0` starts the sum again whenever it passes 2^31 - 1. FX-26's
;;; integers are 61 bits, so `add32` checks the range of each sum and
;;; raises Overflow as an abort to the prompt tag `overflow`; the handler is
;;; a prompt around the sum, per element, as SML's `handle` is.
;;; SML's vector of pairs is an array of products.

(define-type pair (productof (a int) (b int)))

;; SML's Overflow, raised by Int32's +; its handler answers an int.
(define-type overflow-tag (prompt-tag int unit (read (globals add32 overflow)) @x))

(define add32 (poly ((r region)) (subr (goto r) ((prompt-tag int unit (read (globals add32 overflow)) r) int int) int))
  (plambda ((r region))
    (lambda (tag x y)
      (let ((s (+ x y)))
        (if (or (> s 2147483647) (< s -2147483648))
            (abort-current-continuation tag #u)
            s)))))

(define overflow overflow-tag (make-continuation-prompt-tag))

(define* tabulate (subr (maxeff (alloc @v) (write @v) spin) (int (subr pure (int) pair)) (arrayof pair @v))
  (lambda (n f)
    (let ((v (the (arrayof pair @v) (make-array n (product (a 0) (b 0))))))
      (letrec ((fill (subr (maxeff (write @v) spin) (int) unit)
                 (lambda (i) (if (< i n) (begin (array-set! v i (f i)) (fill (+ i 1))) #u))))
        (begin (fill 0) v)))))

;; Vector.foldl, with the benchmark's function fixed.
(define* foldl (subr (maxeff (read @v) spin) ((subr (read (globals add32 overflow)) (pair int) int) int (arrayof pair @v)) int)
  (lambda (f b v)
    (letrec ((loop (subr (maxeff (read @v) spin (read (globals add32 overflow))) (int int) int)
               (lambda (i acc) (if (< i (array-length v)) (loop (+ i 1) (f (array-ref v i) acc)) acc))))
      (loop 0 b))))

;; The inputs, where no compiler can fold them: globals, which a later
;; definition may replace.
(define size int 1000000)
(define iterations int 10)

(define* doit (subr (maxeff (read @v) (alloc @v) (write @v) spin) (int) int)
  (lambda (n)
    (let ((v (tabulate size (lambda (i) (product (a i) (b (+ i 1)))))))
      (letrec ((loop (subr (maxeff (read @v) spin (read (globals add32 foldl overflow))) (int int) int)
                 (lambda (n result)
                   (if (= 0 n)
                       result
                       (loop (- n 1)
                             (foldl (lambda (p c)
                                      (prompt overflow
                                        ((proj add32 @x) overflow ((proj add32 @x) overflow (extract p a) (extract p b)) c)
                                        (lambda (u) 0)))
                                    0 v))))))
        (loop n 0)))))
(doit iterations)
