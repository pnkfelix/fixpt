;; => 6
;; A process that sends itself messages, through its own address, `(self
;; box)`: told 3, it counts down to 0, adding as it goes.
(define total (icell int @c) (make-icell))
(define counter (addr int @p)
  (spawn (box int r)
    (let ((me (self box)))
      (letrec ((go (subr (maxeff (receive r) (send r) (init @c) nondet spin) (int) unit)
                 (lambda (s)
                   (let ((n (receive box)))
                     (if (= n 0)
                         (icell-put! total s)
                         (begin (send me (- n 1)) (go (+ s n))))))))
        (go 0)))))
(send counter 3)
(icell-get total)
