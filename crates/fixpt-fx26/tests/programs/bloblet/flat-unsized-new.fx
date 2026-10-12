;; ! a new blobref's array of a length not literal is of length `finite`
;; A new blobref may not claim a length a size variable names: that could
;; be another array's, and what is learned of it would then be wrong. Its
;; length is named where it is bound (TODO.md §77).
(define-type blob (bloblet (fields) @heap))
(define at
  (poly ((n size)) (subr pure (blob) (blobref blob (arrayof f64 n))))
  (plambda ((n size)) (lambda (b) (the (blobref blob (arrayof f64 n)) (blobref-at b 0)))))
