; `(reset (+ 1 (shift k k)))`: the continuation is aborted to the handler,
; which returns it as the prompt's answer. That changes the answer type from
; int to a continuation, and the tag rules it out. `s`, whose aborts carry a
; continuation, is bound by the test.
(prompt s
  (+ 1 ((proj (proj call-with-composable-continuation @p)
              int (composable int int pure @p) pure int (goto @p))
        (lambda ((k (composable int int pure @p)))
          ((proj (proj abort-current-continuation @p) int (composable int int pure @p) pure) s k))
        s))
  (lambda ((k (composable int int pure @p))) k))
