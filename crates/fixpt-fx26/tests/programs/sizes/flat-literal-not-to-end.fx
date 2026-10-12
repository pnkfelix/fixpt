; Rejected: a blobref to an array of 3 is no blobref to one that runs to
; the end of the suffix: only a length named where such a blobref was
; bound means what `finite` does there (TODO.md §77).
(define-type blob (bloblet (fields) @heap))
(define f (subr pure ((blobref blob (arrayof i64 3))) (blobref blob (arrayof i64 finite)))
  (lambda (r) r))
