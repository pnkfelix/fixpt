;; => 102
;; A collector watches three workers, each monitored (`spawn-monitored`):
;; the second fails (`error`), and the collector is sent its failure as a
;; message, `(sum failed "bad input")`, instead of the program failing. It
;; counts 1 for each answer and 100 for that failure.
(define-type report (sumof (ok int) (failed string)))
(define total (icell int @c) (make-icell))
(define collector (addr report @p)
  (spawn (box report r)
    (letrec ((go (subr (maxeff (receive r) (init @c) nondet spin) (int int) unit)
               (lambda (n score)
                 (if (= n 3)
                     (icell-put! total score)
                     (tagcase (receive box)
                       (ok v (go (+ n 1) (+ score v)))
                       (failed m (go (+ n 1) (+ score (if (string=? m "bad input") 100 50)))))))))
      (go 0 0))))
(define* work (subr spin (int) int) (lambda (k) (if (= k 0) (error "bad input") k)))
(define* failed (subr pure (string) report) (lambda (m) (sum failed m)))
(define* start (subr (maxeff (alloc @w) (send @p) spin nondet) () (addr int @w))
  (lambda ()
    (spawn-monitored collector failed (box int r) (send collector (sum ok (work (receive box)))))))
(define w1 (addr int @w) (start))
(define w2 (addr int @w) (start))
(define w3 (addr int @w) (start))
(send w1 1)
(send w2 0)
(send w3 1)
(icell-get total)
