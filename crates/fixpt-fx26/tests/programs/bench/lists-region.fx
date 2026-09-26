;;; `lists`, each round's list in a region of its own: built with `rcons`,
;;; summed, and given back whole when the round ends.
(define one-round (subr pure (int) int)
  (lambda (n)
    (letrena r
      (letrec ((iota (subr (alloc r) (int (listof int r)) (listof int r))
                 (lambda (n acc) (if (= n 0) acc (iota (- n 1) (rcons r n acc)))))
               (add-up (subr (read r) ((listof int r) int) int)
                 (lambda (xs acc) (if (null? xs) acc (add-up (cdr xs) (+ acc (car xs)))))))
        (add-up (iota n nil) 0)))))
(define rounds (subr pure (int int) int)
  (lambda (k acc) (if (= k 0) acc (rounds (- k 1) (+ acc (one-round 1000))))))
(rounds 3000 0)
