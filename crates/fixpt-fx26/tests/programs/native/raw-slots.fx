;;; `f64`s in raw frame slots (TODO.md §91): `y` lives in one across the
;;; recursive call, through the stack cache's overflows and underflows and
;;; the collections the allocation makes, so frames holding raw words are
;;; flushed, copied and restored; and a slot that holds an `f64`, then an
;;; `int`, in turn (`reuse`), split: the `f64` raw in a slot of its own,
;;; the `int` a value (`reps::split_slots`).
(define* deepf (subr (maxeff (alloc @heap) spin) (int f64) f64)
  (lambda (n x)
    (if (= n 0)
        x
        (let* ((y (f64* x 1.5))
               (z (deepf (- n 1) (f64+ x 1.)))
               (junk (the (listof int @heap) (cons n nil))))
          (f64+ (f64- z y) (f64* y .5))))))
(define* reuse (subr (maxeff (alloc @heap) spin (read (globals deepf))) (int f64) int)
  (lambda (n x)
    (if (= n 0)
        0
        (+ (let ((a (f64* x 2.))) (f64->int (f64-truncate (f64+ a (deepf 3 a)))))
           (+ (let ((b (* n 3))) (+ b (car (the (listof int @heap) (cons b nil)))))
              (reuse (- n 1) x))))))
(define* raw-slots (subr (maxeff (alloc @heap) spin (read (globals deepf reuse))) (int) int)
  (lambda (n) (+ (f64->int (f64-truncate (f64* (deepf n 1.) 1e-3))) (reuse 50 1.25))))
(raw-slots 3000)
