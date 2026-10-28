;; ! argument 1 is a (listof int @r.1), where a (listof int acyclic) is expected
;; A list joined with `nil` in an `if` (Heist's report, 2026-10-28): a pair
;; that may be `nil`, whose tail is a list of the same, is that list, and
;; both checkers show it so in the message.
(define* f (subr pure ((listof int acyclic)) int) (lambda (l) 0))
(define* g (subr pure (int) int) (lambda (n) (let ((l (if (> n 0) (list n) nil))) (f l))))
0
