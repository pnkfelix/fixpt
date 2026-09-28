;;; Globals are a region only in effects: they are read and written, and
;;; hold no data.
(define xs (listof int @globals) nil)
(define f (subr (alloc @globals) () int) (lambda () 1))
