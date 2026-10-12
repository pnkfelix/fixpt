; Rejected: an array of a length not known is of no length in particular:
; not of 5, whatever it is made of (TODO.md §77, N5c).
(define f (subr pure ((arrayof int @heap)) (narrayof int 5 @heap)) (lambda (a) a))
