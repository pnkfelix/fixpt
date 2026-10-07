; Accepted: `null?` narrows a variable: in its `else` a list is a pair, not
; `nil`, and so fits a `pairof` (`docs/research/logical-types.md`, L0).
(define-type ints (listof int @r))
(define* head (subr (read @r) ((pairof int ints @r)) int) (lambda (p) (car p)))
(define* first (subr (maxeff (read @r) (read (globals head))) (ints) int)
  (lambda (xs) (if (null? xs) 0 (head xs))))
(first (list 7 8))
