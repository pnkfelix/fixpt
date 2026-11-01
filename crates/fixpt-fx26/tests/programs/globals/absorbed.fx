;;; `(read @globals)` with `spin` absorbs the reads of single globals that
;;; `define*` finds: they say nothing more (`Effect::absorbed`). Without
;;; `spin` they stay (`->*` finds by them that a procedure reaches itself).
(define limit int 10)
(define below (subr (read (globals limit)) (int) bool) (lambda (x) (< x limit)))
(define* busy (subr (maxeff spin (read @globals)) (int) int) (lambda (x) (if (below x) x limit)))
(define* calm (subr (read @globals) (int) int) (lambda (x) (if (below x) x limit)))
