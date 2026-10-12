; Rejected: a `make-array` of 5 is no array of 6 (TODO.md §77, N5c).
(define six (narrayof int 6 @heap) (make-array 5 0))
