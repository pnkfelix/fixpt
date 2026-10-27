;; Frames keeping values, under a loop, to stop in: `keep`'s each keeps
;; the head of its list across its call.
(define* spin (subr spin (int) int)
  (lambda (n) (if (= n 0) (spin 1) (spin (+ n 1)))))
(define* keep (subr (maxeff (read @l) (alloc @l) spin) (int (listof int @l)) int)
  (lambda (k xs)
    (if (= k 0)
        (spin 1)
        (+ (car xs) (keep (- k 1) (cons k xs))))))
(define* say (subr (io stdout) (string) unit) (lambda (s) (begin (write-out s) #u)))
(say "ready\n")
(keep 3 (list 10 20))
