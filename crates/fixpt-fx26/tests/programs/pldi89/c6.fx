; C6: a continuation stored where the caller can reach it.
(begin ((proj (proj (proj cwcc @k) unit) (write @x))
        (lambda ((f (subr (goto @k) (unit) void)))
          ((proj (proj set @x) (subr pure () (subr (goto @k) (unit) void)))
           x
           (lambda () f))))
       (h))
