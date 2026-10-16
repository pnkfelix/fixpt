; Rejected: a module's `->*` lambda is bound at its placeholder until
; every value is made, so a value made by calling it would be checked at
; an effect not yet found.
(define m (module (define f (->* (int) int) (lambda (x) (+ x 1)))
                  (define y int (f 1))))
(with m y)
