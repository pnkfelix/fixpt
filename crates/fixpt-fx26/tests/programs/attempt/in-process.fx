;; => 15
;; An attempt in a process: its failure is caught there, and the process
;; goes on to answer.
(define answer (icell int @c) (make-icell))
(define w (addr int @p)
  (spawn (box int r)
    (let ((n (receive box)))
      (icell-put! answer (+ (attempt (quotient 10 n) (lambda ((m string)) 5)) 10)))))
(send w 0)
(icell-get answer)
