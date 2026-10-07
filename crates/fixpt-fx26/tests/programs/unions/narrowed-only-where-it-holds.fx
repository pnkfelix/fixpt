; Rejected: `null?` narrows only its `else`: in its `then` the list is still
; one that may be `nil`.
(define-type ints (listof int @r))
(define* head (subr (read @r) ((pairof int ints @r)) int) (lambda (p) (car p)))
(define* first (subr (maxeff (read @r) (read (globals head))) (ints) int)
  (lambda (xs) (if (null? xs) (head xs) 0)))
(first (list 7))
