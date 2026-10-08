; Accepted: `false`, the type of `#f` alone, below `bool` and of its shape:
; a member of unions, "an int or none", that `bool?` takes apart; `#f`
; checks as one where one is expected, and is a `bool` everywhere else.
(define-type maybe-int (union false int))
(define* next (subr pure (maybe-int) int) (lambda (x) (if (bool? x) 0 (+ x 1))))
(define* none (subr pure () maybe-int) (lambda () #f))
(define* as-bool (subr pure () bool) (lambda () (the false #f)))
(next (none))
