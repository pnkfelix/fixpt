; Rejected, though it ends after one call: `n` is passed on as `i`, not as
; itself, so no bound stays put, and the analysis sees no measure fall.
(define f (subr pure (int int) int) (lambda (i n) (if (< i n) (f n (+ i 1)) i)))
