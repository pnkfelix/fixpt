;; => (#:b #:a)
;; A `tagcase` arm takes a positional product apart, its names in order.
(define-type shape (sumof (#:pt (tupleof keyword keyword))))
(define flip (subr pure (shape) (listof keyword acyclic))
  (lambda (s) (tagcase s (#:pt (x y) (list y x)))))
(flip (sum #:pt (tuple #:a #:b)))
