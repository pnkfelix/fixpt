; Rejected: the continuation is kept, and called after `cwcc` has returned,
; so it comes back to it again and again: `loop` may not end and must say
; `spin` (docs/research/soundness-findings.md, F3).
(define loop (subr pure () int)
  (lambda ()
    (let ((c (the (icell (subr (goto @k) (int) void) @c) (make-icell))))
      (begin
        ((proj (proj (proj cwcc @k) int) (write @c))
          (lambda ((k (subr (goto @k) (int) void))) (begin (icell-put! c k) 0)))
        ((icell-get c) 0)))))
