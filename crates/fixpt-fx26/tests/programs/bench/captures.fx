;;; Capture and resume a composable continuation many times, each from 20
;;; calls deep: the handler gets the continuation and calls it at once.
(define t (prompt-tag int (composable int int spin @p) (maxeff spin (read (globals deep t))) @p) (make-continuation-prompt-tag))
(define* deep (subr (maxeff (goto @p) (comefrom @p) spin) (int) int)
  (lambda (d)
    (if (= d 0)
        ((proj (proj call-with-composable-continuation @p)
               int (composable int int spin @p) spin int (maxeff (goto @p) (read (globals t))))
         (lambda ((k (composable int int spin @p)))
           ((proj (proj abort-current-continuation @p) int (composable int int spin @p) spin) t k))
         t)
        (+ 1 (deep (- d 1))))))
(define* rounds (subr (maxeff (goto @p) (comefrom @p) spin) (int int) int)
  (lambda (n acc)
    (if (= n 0)
        acc
        (rounds (- n 1) (+ acc (prompt t (deep 20) (lambda ((k (composable int int spin @p))) (k 1))))))))
(rounds 20000 0)
