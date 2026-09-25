(define (nontail n)
  (with-continuation-mark 'depth n
    (if (= n 0)
        (continuation-mark-set->list (current-continuation-marks) 'depth)
        (car (list (nontail (- n 1)))))))
(nontail 3)
