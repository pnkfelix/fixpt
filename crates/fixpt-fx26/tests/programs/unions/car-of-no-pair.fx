;;; A union with no pair member is no pair: `car` of one is refused.
(define x (union int bool) 3)
(car x)
