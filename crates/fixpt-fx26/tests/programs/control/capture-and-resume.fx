; Capture the rest of the body up to the prompt, and run it twice. Calling
; `k` has control effects on @p, but only inside the prompt, which
; delimits them.
(prompt t
  (+ 1 ((proj (proj call-with-composable-continuation @p)
              int int pure int (maxeff (goto @p) (comefrom @p)))
        (lambda ((k (composable int int pure @p))) (k (k 1)))
        t))
  (lambda ((v int)) v))
