; C4, the outer `cwcc`'s argument.

; A continuation returned as its own result.
(define-type K (subr (goto @k) (K) void))

(lambda ((f K))
  ((proj (proj (proj cwcc @k) K) (maxeff (goto @k) spin))
   (lambda ((g K)) (f g)))
  (h)
  f)
