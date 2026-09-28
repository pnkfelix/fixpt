;;; Lists: built, reversed and summed, many times.
(define* iota (subr (maxeff (alloc @l) spin) (int (listof int @l)) (listof int @l))
  (lambda (n acc) (if (= n 0) acc (iota (- n 1) (cons n acc)))))
(define* add-up (subr (maxeff (read @l) spin) ((listof int @l) int) int)
  (lambda (xs acc) (if (null? xs) acc (add-up (cdr xs) (+ acc (car xs))))))
(define* rounds (subr (maxeff (read @l) (alloc @l) spin) (int int) int)
  (lambda (k acc) (if (= k 0) acc (rounds (- k 1) (+ acc (add-up (iota 1000 nil) 0))))))
(rounds 3000 0)
