;; => 3
;; An `include`'s type family applied in the module's items' types
;; (`TODO.md` §69): `box` is `boxes`'s.
(define boxes (module (define-type (box (k type) (r region)) (pairof k k r))
                      (define mk (subr pure (int) int) (lambda (x) x))))
(define m
  (module
    (include boxes)
    (define sum (subr (read @heap) ((box int @heap)) int) (lambda (b) (+ (car b) (cdr b))))
    (define-type ib (box int @heap))
    (define first (subr (read @heap) (ib) int) (lambda (b) (car b)))))
((with m sum) (cons 1 2))
