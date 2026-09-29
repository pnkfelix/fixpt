;;; IMP-FOR -- an imperative `for` loop over a ref, taking a closure, nested
;;; seven deep, counting to 10000000 in a ref.
;;;
;;; From MLton's benchmark suite (benchmark/tests/imp-for.sml, commit
;;; aa2fd1ad9b91), ported to FX-26. Iteration count (ours; MLton's driver
;;; was not fetched): (doit 10), counting to 10000000 10 times.
;;; Answer: 10000000, the count (the original checks for it).
;;; The closures' effect is fixed, not polymorphic: whatever the heap allows,
;;; and reading globals (they call `for`).

(define-type body (subr (maxeff (read @h) (write @h) (alloc @h) spin (read @globals)) (int) unit))

(define for (subr (maxeff (read @h) (write @h) (alloc @h) spin (read @globals)) (int int body) unit)
  (lambda (start stop f)
    (let ((i (the (ref int @h) (new start))))
      (letrec ((loop (subr (maxeff (read @h) (write @h) (alloc @h) spin (read @globals)) () unit)
                 (lambda ()
                   (if (>= (get i) stop)
                       #u
                       (begin (f (get i)) (set i (+ (get i) 1)) (loop))))))
        (loop)))))

(define doit1 (subr (maxeff (read @h) (write @h) (alloc @h) spin (read @globals)) () int)
  (lambda ()
    (let ((x (the (ref int @h) (new 0))))
      (begin
        (for 0 10 (lambda (_)
        (for 0 10 (lambda (_)
        (for 0 10 (lambda (_)
        (for 0 10 (lambda (_)
        (for 0 10 (lambda (_)
        (for 0 10 (lambda (_)
        (for 0 10 (lambda (_)
             (set x (+ (get x) 1))))))))))))))))
        (get x)))))

;; The input, where no compiler can fold it: a global, which a later
;; definition may replace.
(define iterations int 10)

;; MLton's doit: `for (0, size, fn _ => doit ())`; the last count is kept.
(define doit (subr (maxeff (read @h) (write @h) (alloc @h) spin (read @globals)) (int) int)
  (lambda (size)
    (let ((result (the (ref int @h) (new -1))))
      (begin
        (for 0 size (lambda (_) (set result (doit1))))
        (get result)))))
(doit iterations)
