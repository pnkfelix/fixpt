; Rejected: a `pairof` is a pair, never `nil`: a list, which may be `nil`,
; does not fit one where no test has narrowed it.
(define-type ints (listof int @r))
(define* head (subr (read @r) ((pairof int ints @r)) int) (lambda (p) (car p)))
(define* first (subr (maxeff (read @r) (read (globals head))) (ints) int)
  (lambda (xs) (head xs)))
(first (list 7))
