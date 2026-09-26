;;; `rcons` in a region a `letrena` binds, by helpers the body makes:
;;; the list in the region, its sum given back. Called many times, so that
;;; regions are entered, filled and ended again.
(define sum-to (subr pure (int) int)
  (lambda (n)
    (letrena r
      (letrec ((build (subr (alloc r) (int (listof int r)) (listof int r))
                 (lambda (i acc) (if (= i 0) acc (build (- i 1) (rcons r i acc)))))
               (add-up (subr (read r) ((listof int r) int) int)
                 (lambda (xs acc) (if (null? xs) acc (add-up (cdr xs) (+ acc (car xs)))))))
        (add-up (build n nil) 0)))))

(define total (subr pure (int int) int)
  (lambda (i acc) (if (= i 0) acc (total (- i 1) (+ acc (sum-to 10))))))

(total 1000 0)
