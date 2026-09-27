;;; A `letreap`: a region collected while its body runs. Each round builds
;;; lists in the reap and keeps only the last, so most of what the reap is
;;; given is garbage the collector drops, and the reap stays small.
(define churn (subr spin (int) int)
  (lambda (rounds)
    (letreap r
      (letrec ((build (subr (maxeff (alloc r) (read r) spin) (int (listof int r)) (listof int r))
                 (rlambda r (i acc) (if (= i 0) acc (build (- i 1) (rcons r i acc)))))
               (add-up (subr (maxeff (read r) spin) ((listof int r) int) int)
                 (rlambda r (xs acc) (if (null? xs) acc (add-up (cdr xs) (+ acc (car xs))))))
               (go (subr (maxeff (alloc r) (read r) spin) (int (listof int r)) int)
                 (rlambda r (k kept)
                   (if (= k 0) (add-up kept 0) (go (- k 1) (build 1000 nil))))))
        (go rounds nil)))))

(churn 300)
