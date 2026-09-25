; The same capture with the answer type kept: the handler applies the
; continuation instead of returning it. It checks, and since the handler
; runs outside the prompt, its call of `k` keeps its control effects.
(prompt s
  (+ 1 ((proj (proj call-with-composable-continuation @p)
              int (composable int int pure @p) pure int (goto @p))
        (lambda ((k (composable int int pure @p)))
          ((proj (proj abort-current-continuation @p) int (composable int int pure @p) pure) s k))
        s))
  (lambda ((k (composable int int pure @p))) (k 10)))
