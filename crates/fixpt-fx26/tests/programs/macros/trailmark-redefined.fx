;; ! a use of `pick`: `via` where the trailmark `via` is written
;; A macro defined with a trailmark's name: the name no longer is one, and a
;; macro's pattern that names it no longer matches it.
(define-syntax via (trailmark))
(define-syntax pick (syntax-rules #:trailmarks (via) ((_ e via d) (if e 1 d))))
(define-syntax via (syntax-rules ((_) 0)))
(pick #t via 7)
