;;; Boxes made where native code cannot collect (`TODO.md` §102): `twice`,
;;; a global's procedure, reaches `loop` as a value, so each call boxes its
;;; `f64` argument, which the call-out that boxes it past the nursery's end
;;; may not collect for. No other call-out in the loop: the next poll
;;; collects, so the nursery is collected as it fills, not left to grow.
(define twice (->* (f64) f64) (lambda (x) (f64* x 2.)))
(define loop (->* ((subr pure (f64) f64) int f64) f64)
  (lambda (f i acc) (if (= i 0) acc (loop f (- i 1) (f64+ acc (f (int->f64 i)))))))
(f64->int (loop twice 2000000 0.))
