; Rejected: a composable continuation kept in a cell its own computation
; reads could compose itself forever: the knot rule refuses it.
(define loop (subr pure () int)
  (lambda ()
    (let ((c (the (icell (composable int int (read @c) @p) @c) (make-icell)))
          (t ((proj (proj make-continuation-prompt-tag @p) int int (read @c)))))
      (prompt t
        (+ 1 (begin ((proj (proj call-with-composable-continuation @p) int int (read @c) int (write @c))
                     (lambda ((k (composable int int (read @c) @p))) (begin (icell-put! c k) 0))
                     t)
                    ((icell-get c) 1)))
        (lambda ((v int)) v)))))
(loop)
