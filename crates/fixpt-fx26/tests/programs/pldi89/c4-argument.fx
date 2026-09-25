; C4, the outer `cwcc`'s argument. `{K}` is filled in by the test: the type
; of a continuation returned as its own result.
(lambda ((f {K}))
  ((proj (proj (proj cwcc @k) {K}) (goto @k))
   (lambda ((g {K})) (f g)))
  (h)
  f)
