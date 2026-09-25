; An abort to the prompt's own tag is caught by the prompt, so the prompt
; has no control effect on @p. `t : (prompt-tag int int pure @p)` is bound
; by the test.
(prompt t
  (+ 1 ((proj (proj abort-current-continuation @p) int int pure) t 5))
  (lambda ((v int)) v))
