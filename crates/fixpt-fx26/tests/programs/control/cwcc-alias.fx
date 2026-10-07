; Rejected: `cwcc` named only to call it (F15). Bound to another name, its
; call escaped F3's rule, and this `pure` procedure looped forever.
(define loop (subr pure () int)
  (lambda ()
    (let ((c (the (icell (subr (goto @k) (int) void) @c) (make-icell)))
          (callcc cwcc))
      (begin
        ((proj (proj (proj callcc @k) int) (write @c))
          (lambda ((k (subr (goto @k) (int) void))) (begin (icell-put! c k) 0)))
        ((icell-get c) 0)))))
