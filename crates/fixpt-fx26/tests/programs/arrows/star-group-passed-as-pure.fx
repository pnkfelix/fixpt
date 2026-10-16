; Rejected: `->*` finds `count` may not end, so it is no `(-> (int) int)`,
; which `twice` takes; the check at the types found refuses it.
(define twice (-> ((-> (int) int) int) int) (lambda (g x) (g (g x))))
(define f (-> (int) int)
  (lambda (n)
    (letrec ((count (->* (int) int) (lambda (k) (if (= k 0) 0 (twice count (- k 1))))))
      (count n))))
(f 3)
