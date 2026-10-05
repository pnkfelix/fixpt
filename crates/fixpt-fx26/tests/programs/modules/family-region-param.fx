;; => 1
;; A family whose body applies a module's family to its own region
;; parameter: the parameter, bound to a region while the family expands, is
;; read as one (`TODO.md` §34).
(define m (module
  (define-type (box (k type) (r region)) (pairof k k r))
  (define mk (subr pure (int) int) (lambda (x) x))))
(define-type (box (k type) (r region)) ((select m box) k r))
(define f (subr (read @heap) ((box int @heap)) int) (lambda (b) (car b)))
(f (cons 1 2))
