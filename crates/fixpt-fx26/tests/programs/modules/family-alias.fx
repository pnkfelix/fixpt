;; => 1
;; A module's type family named outside it, `(define-type box (select m
;; box))`, applied as the family is: as `((select m box) int @heap)`
;; (`TODO.md` §34).
(define m (module
  (define-type (box (k type) (r region)) (pairof k k r))
  (define mk (subr pure (int) int) (lambda (x) x))))
(define-type box (select m box))
(define f (subr (read @heap) ((box int @heap)) int) (lambda (b) (car b)))
(f (cons 1 2))
