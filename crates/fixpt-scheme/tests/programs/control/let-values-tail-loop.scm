(define (loop n)
  (with-continuation-mark 'k n
    (if (= n 0)
        (continuation-mark-set->list (current-continuation-marks) 'k)
        (let-values (((a b) (values (- n 1) 0))) (loop a)))))
(loop 4)
