; A tag made for this prompt alone. `u` is another tag in @p, bound by the
; test, so a body that aborts to it keeps its `goto`.
(prompt ((proj (proj make-continuation-prompt-tag @p) int int pure))
  ((proj (proj abort-current-continuation @p) int int pure) u 5)
  (lambda ((v int)) v))
