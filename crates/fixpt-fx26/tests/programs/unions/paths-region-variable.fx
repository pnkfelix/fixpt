; Rejected: a write to a region variable may be a write to any region, the
; path's among them, so it ends what a test showed.
(define-type cell (pairof (union int string) int @r))
(define* plus (poly ((s region)) (subr (maxeff (read @r) (write s)) (cell (ref int s)) int))
  (plambda ((s region))
    (lambda (x b) (if (int? (car x)) (begin (set b 1) (+ (car x) 1)) 0))))
