(define (loop n)
  (with-continuation-mark 'depth n
    (if (= n 0)
        (continuation-mark-set->list (current-continuation-marks) 'depth)
        (loop (- n 1)))))
