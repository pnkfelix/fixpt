; Rejected: bounds that do not meet (`TODO.md` §66). `a`'s elements are
; `int`s, exactly, and a `string` is expected of one: no element type is
; both at least `int` and at most `string`.
(define a (arrayof int @r) (make-array 3 7))
(define* s (subr (read @r) (int) string) (lambda (i) (array-ref a i)))
s
