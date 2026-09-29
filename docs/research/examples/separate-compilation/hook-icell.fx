;;; A knot across files, in FX-26 today: an earlier file calls a procedure
;;; that a later file supplies, through an I-cell. The earlier file runs
;;; first, and its type says it waits on the cell.

;;; ---- log.fx : runs first; calls a hook it does not define ----
(private-regions @h)
(define hook (icell (subr pure (int) int) @h) (make-icell))
(define* twice-hooked (subr (await @h) (int) int)
  (lambda (n) ((icell-get hook) ((icell-get hook) n))))

;;; ---- app.fx : imports log.fx, and ties the knot ----
(icell-put! hook (lambda ((n int)) (* n 2)))
(twice-hooked 3)                          ; 12
