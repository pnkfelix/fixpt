; Rejected: a write to the region a path reads through ends what a test
; showed of it (`set-car!` may have put a string there).
(define-type cell (pairof (union int string) int @r))
(define* plus (subr (maxeff (read @r) (write @r)) (cell) int)
  (lambda (x) (if (int? (car x)) (begin (set-car! x "s") (+ (car x) 1)) 0)))
