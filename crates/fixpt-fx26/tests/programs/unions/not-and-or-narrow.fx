; Accepted: narrowing through `not`, `and` and `or`, as the size facts go:
; the `then` of `(not (null? xs))`, of an `and` both of whose tests hold, and
; the `else` of an `or` neither of whose tests does.
(define-type ints (listof int @r))
(define* head (subr (read @r) ((pairof int ints @r)) int) (lambda (p) (car p)))
(define-effect heads (maxeff (read @r) (read (globals head))))
(define* by-not (subr heads (ints) int) (lambda (xs) (if (not (null? xs)) (head xs) 0)))
(define* by-and (subr heads (ints) int)
  (lambda (xs) (if (and (not (null? xs)) (> (car xs) 0)) (head xs) 0)))
(define* by-or (subr heads (ints) int)
  (lambda (xs) (if (or (null? xs) (< (car xs) 0)) 0 (head xs))))
(+ (by-not (list 1)) (+ (by-and (list 2)) (by-or (list 3))))
