; Rejected: `->*` finds `f` reads itself and may not end, so `f` is no
; `(-> (int) int)`, which `twice` takes: the call of itself stood for
; nothing while its effect was found, and the check at the type found
; refuses it.
(define twice (-> ((-> (int) int) int) int) (lambda (g x) (g (g x))))
(define f (->* (int) int) (lambda (n) (if (<= n 0) 0 (twice f (- n 1)))))
(f 3)
