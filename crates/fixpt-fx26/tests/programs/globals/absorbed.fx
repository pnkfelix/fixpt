;;; `(read @globals)` absorbs the reads of single globals that `define*`
;;; finds: they say nothing more (`Effect::absorbed`). A global reading
;;; `@globals` says `spin`, as it may read itself; one that does not is
;;; refused.
(define limit int 10)
(define below (subr (read (globals limit)) (int) bool) (lambda (x) (< x limit)))
(define* busy (subr (maxeff spin (read @globals)) (int) int) (lambda (x) (if (below x) x limit)))
(define* calm (subr (read @globals) (int) int) (lambda (x) (if (below x) x limit)))
