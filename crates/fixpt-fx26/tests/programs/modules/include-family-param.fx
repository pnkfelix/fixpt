;; => "b"
;; A family a module included gives, applied to a procedure's parameter:
;; `(box thing)` is `box` applied, never a parameter named `box` (Heist's).
(define before (module (define-type (box (s type)) (tupof (state (ref s @ed)) (name string)))))
(define m (module (include before) (define-type thing (tupof (n int)))
                  (define take (subr pure ((box thing)) string) (lambda (b) (extract b name)))))
((with m take) (tup (state (new (tup (n 1)))) (name "b")))
