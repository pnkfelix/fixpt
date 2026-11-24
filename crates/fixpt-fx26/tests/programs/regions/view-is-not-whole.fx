; Rejected: a view (TODO.md §310) is not a whole buffer: a `(strof r)`
; may be a slice, and goes where a `(stringof r)` is wanted no more than a
; `str` goes where a `string` is.
(define* whole (poly ((r region)) (subr pure ((stringof r)) unit)) (lambda (s) #u))
(define* f (poly ((r region)) (subr pure ((strof r)) unit)) (lambda (s) (whole s)))
