; Rejected: a blobref to an array that runs to the end is not one of the
; length a parameter's was given where it was bound: that length is its
; own blobref's (TODO.md §77).
(define-type blob (bloblet (fields) @heap))
(define-type arr (blobref blob (arrayof i64 finite)))
(define f (poly ((n size))
            (subr pure ((blobref blob (arrayof i64 n)) (blobref blob (arrayof i64 n))) (nat n)))
  (plambda ((n size)) (lambda (a b) (blobref-length b))))
(define g (subr (read (globals f)) (arr arr) nat)
  (lambda (s t) (f s t)))
