; Rejected: `->*` is only the type a `define` declares; a parameter's
; type says its effect.
(define ap (-> ((->* (int) int) int) int) (lambda (f x) (f x)))
(ap (lambda (x) x) 1)
