; Rejected: `f` gives itself away, and whoever calls it may loop through
; it with no recursive call in sight; so naming it says `spin`.
(define f (subr pure (int) int) (lambda (x) ((lambda ((h (subr pure (int) int))) (h x)) f)))
