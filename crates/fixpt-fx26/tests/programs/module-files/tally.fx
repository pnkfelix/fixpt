;; A module's file of a region parameter (`(module-parameters ((name kind)
;; …))`): whoever loads it gives the region its count is in, and each call
;; of what it loads as makes another count.
(module-parameters ((r region)))
(define count (ref int r) (new 0))
(define tick (subr (maxeff (read r) (write r)) () int)
  (lambda () (begin (set count (+ (get count) 1)) (get count))))
