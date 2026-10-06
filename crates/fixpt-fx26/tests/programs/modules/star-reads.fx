;; => #t
;; `define*` in a module, as at the top level: the globals a procedure
;; reads, outside the module, found and put in its type; a module's own
;; names are not globals. `both`, after `under?`, sees its type found.
(define limit int 10)
(define m (module
  (define small? (subr pure (int) bool) (lambda (x) (< x 3)))
  (define* under? (subr pure (int) bool) (lambda (x) (and (small? x) (< x limit))))
  (define* both (subr pure (int) bool) (lambda (x) (under? x)))))
(with m (both 2))
