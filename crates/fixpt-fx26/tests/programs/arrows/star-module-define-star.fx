; Rejected: in a module too, `define*` and `->*` each find what a
; procedure does.
(define m (module (define* f (->* (int) int) (lambda (x) (+ x 1)))))
((with m f) 1)
