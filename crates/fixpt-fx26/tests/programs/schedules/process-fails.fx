;; A process that writes an I-cell twice fails, which fails the form whose
;; run it was in (`(send w 0)`); the next form runs as ever.
(define c (icell int @c) (make-icell))
(define w (addr int @w)
  (spawn (box int p) (begin (receive box) (icell-put! c 1) (icell-put! c 2))))
(send w 0)
(let ((d (the (icell int @d) (make-icell))))
  (par ((a (+ 1 (icell-get d))) (b (begin (icell-put! d 2) 0))) (+ a b)))
