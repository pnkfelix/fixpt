;; ! a int is expected here, and this is a cell
;; A re-exported value's type names a re-exported type by its name even when
;; nothing has named that type since: the alias, declared ahead of the
;; module, is linked to it as soon as the module is bound.
(define m (module (define-type cell (productof (1 int)))
                  (define mk (subr pure (int) cell) (lambda (n) (product (1 n))))))
(define-type cell (select m cell))
(define mk (with m mk))
(+ (mk 1) 1)
