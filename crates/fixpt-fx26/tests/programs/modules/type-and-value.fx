;; => 7
;; A module's value may have a type's name, as at the top level: types and
;; values are named apart, in a module and in a `moduleof` alike.
(define m (module (define-type cell (productof (1 int)))
                  (define cell (subr pure (int) cell) (lambda (n) (product (1 n))))))
(define-type cell (select m cell))
(define cell (with m cell))
(define k (subr pure ((moduleof (desc box int) (val box int))) int) (lambda (x) (with x box)))
(+ (extract (cell 3) 1) (k (module (define-type box int) (define box int 4))))
