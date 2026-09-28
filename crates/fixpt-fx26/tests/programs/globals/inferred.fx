;;; `define*` finds the globals a procedure reads, precisely: those its body
;;; names, and those the procedures it calls read, its own name included
;;; when it calls itself.
(define limit int 10)
(define* below (subr pure (int) bool) (lambda (x) (< x limit)))
(define* clamp (subr pure (int) int) (lambda (x) (if (below x) x limit)))
(define* count (subr spin (int) int) (lambda (n) (if (below n) (count (+ n 1)) n)))
(clamp 12)
