; C7. A continuation that takes a pair of continuations, and that pair: two
; types defined in terms of each other, so the first is a `dletrec`.
(define-type k (dletrec ((p (pairof k k @p)) (k (subr (goto @k) (p) void))) k))
(define-type p (pairof k k @p))

((proj (proj (proj cwcc @k) p)
       (maxeff (alloc @p) (comefrom @k) (write @p) (read @p) (goto @k) spin))
 (lambda ((f k))
   (let ((y ((proj (proj cons @p) k k) f f)))
     ((proj (proj (proj cwcc @k) p) (maxeff (write @p) (goto @k) spin))
      (lambda ((g k))
        ((proj (proj set-cdr! @p) k k) y g)
        (f y)))
     (((proj (proj car @p) k k) y) y))))
