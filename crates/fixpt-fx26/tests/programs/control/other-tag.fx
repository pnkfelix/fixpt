; The body aborts to `u`, another tag in @p, which this prompt does not
; catch: the `goto` must stay. `t` and `u` are bound by the test.
(prompt t
  (+ 1 ((proj (proj abort-current-continuation @p) int int pure) u 5))
  (lambda ((v int)) v))
