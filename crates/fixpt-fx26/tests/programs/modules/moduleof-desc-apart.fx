;; => 9
;; A transparent component written apart from its binder: its label `d`
;; outside, `inner` to the items after it, beside an outer `d`.
(define-type d bool)
(define m (the (moduleof (desc #:d inner int) (val #:x inner) (val #:flag d))
               (module (define-type d int) (define x d 9) (define flag bool #t))))
(define y (select m d) (with m x))
y
