; Rejected: the continuation `k` is only called, but the receiver also
; captures a composable continuation whose segment calls `k`: composed
; after `cwcc` returns, it comes back to it again and again, so the `cwcc`
; call says `spin`, which the tag does not allow (F9).
(define-effect D (maxeff (write @d) (goto @k) (comefrom @k)))
(define loop (subr pure () int)
  (lambda ()
    (let ((c (the (icell (composable int int D @p) @d) (make-icell)))
          (t ((proj (proj make-continuation-prompt-tag @p) int int D))))
      (begin
        (prompt t
          ((proj (proj (proj cwcc @k) int) (maxeff (write @d) (comefrom @p) (goto @k)))
            (lambda ((k (subr (goto @k) (int) void)))
              (begin
                ((proj (proj call-with-composable-continuation @p) int int D int (write @d))
                  (lambda ((j (composable int int D @p))) (begin (icell-put! c j) 0))
                  t)
                (k 0))))
          (lambda ((v int)) v))
        ((icell-get c) 0)))))
