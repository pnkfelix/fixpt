;; => 5
;; A top-level `define-rec` whose types name a module's.
(define counter
  (module
    (define-generative t int)
    (define zero t (up-t 0))
    (define inc (subr pure (t) t) (lambda (c) (up-t (+ (down-t c) 1))))
    (define value (subr pure (t) int) (lambda (c) (down-t c)))))
(define-rec
  (count (subr (maxeff (read (globals count counter)) spin)
               ((select counter t) int) (select counter t))
    (lambda (c k) (if (= k 0) c (count (with counter (inc c)) (- k 1))))))
(with counter (value (count zero 5)))
