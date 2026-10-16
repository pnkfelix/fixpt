; Rejected: `->*` is only the type a `define` declares, not yet a
; `define-rec` group's.
(define-rec (ev? (->* (nat) bool) (lambda (n) (if (= n 0) #t (od? (- n 1)))))
            (od? (->* (nat) bool) (lambda (n) (if (= n 0) #f (ev? (- n 1))))))
(ev? 4)
