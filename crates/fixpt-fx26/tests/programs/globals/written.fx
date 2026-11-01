;;; `define` says what a procedure reads, as any effect: precisely, as
;;; `@globals` (with `spin`: it may read itself), or not at all, which is an
;;; error when it reads one.
(define limit int 10)
(define below (subr (read (globals limit)) (int) bool) (lambda (x) (< x limit)))
(define clamp (subr (maxeff (read @globals) spin) (int) int) (lambda (x) (if (below x) x limit)))
(define wrong (subr pure (int) bool) (lambda (x) (below x)))
