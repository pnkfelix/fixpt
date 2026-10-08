; Rejected: a path no test has narrowed is of its type, a union.
(define-type cell (pairof (union int string) int @r))
(define* plus (subr (read @r) (cell) int) (lambda (x) (+ (car x) 1)))
