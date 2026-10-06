;; => 42
;; A type given to `proj` has its `select`s resolved, as an annotation's
;; are: `box` names `cell`, a module's type re-exported.
(define m (module (define-type cell (productof (1 int))) (define x int 1)))
(define-type cell (select m cell))
(define-type box (productof (1 cell) (2 int)))
(define id (poly ((t type)) (subr pure (t) t)) (plambda ((t type)) (lambda (v) v)))
(define b box (product (1 (product (1 41))) (2 1)))
(let ((c ((proj id box) b))) (+ (extract (extract c 1) 1) (extract c 2)))
