;;; Capture and resume a composable continuation many times, each from 20
;;; calls deep: the handler gets the continuation and calls it at once.
(define t (prompt-tag int (composable int int pure @p) pure @p) (make-continuation-prompt-tag))
(define deep (subr (maxeff (goto @p) (comefrom @p)) (int) int)
  (lambda (d)
    (if (= d 0)
        ((proj (proj call-with-composable-continuation @p)
               int (composable int int pure @p) pure int (goto @p))
         (lambda ((k (composable int int pure @p)))
           ((proj (proj abort-current-continuation @p) int (composable int int pure @p) pure) t k))
         t)
        (+ 1 (deep (- d 1))))))
(define rounds (subr (maxeff (goto @p) (comefrom @p)) (int int) int)
  (lambda (n acc)
    (if (= n 0)
        acc
        (rounds (- n 1) (+ acc (prompt t (deep 20) (lambda ((k (composable int int pure @p))) (k 1))))))))
(rounds 20000 0)
