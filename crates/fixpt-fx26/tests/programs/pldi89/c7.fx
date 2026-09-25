; C7. `{p}` and `{k}` are filled in by the test: the pair of continuations
; and one continuation, as recursive types.
((proj (proj (proj cwcc @k) {p})
       (maxeff (alloc @p) (comefrom @k) (write @p) (read @p) (goto @k)))
 (lambda ((f {k}))
   (let ((y ((proj (proj cons @p) {k} {k}) f f)))
     ((proj (proj (proj cwcc @k) {p}) (maxeff (write @p) (goto @k)))
      (lambda ((g {k}))
        ((proj (proj set-cdr! @p) {k} {k}) y g)
        (f y)))
     (((proj (proj car @p) {k} {k}) y) y))))
