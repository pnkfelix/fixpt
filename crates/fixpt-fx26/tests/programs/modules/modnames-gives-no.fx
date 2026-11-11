;; ! the module gives no `z`
;; A `modnames` names only what the module gives.
(define m (module (define x int 1)))
(define s (modnames x z) m)
