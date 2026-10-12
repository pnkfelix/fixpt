;; ! which takes something of the size of `s`
;; A length named where a blobref is bound means nothing outside the scope
;; that named it. A procedure that takes an array of that length may not
;; leave it: an array of any length could then be given it (TODO.md §77;
;; docs/research/soundness-findings.md, F8).
(define-type blob (bloblet (fields) @heap))
(define-type (samples (n size)) (blobref blob (arrayof f64 n)))
(define reader-for
  (poly ((n size)) (subr pure ((samples n)) (subr (read @heap) ((samples n)) f64)))
  (plambda ((n size)) (lambda (s) (lambda (t) (blobref-get (blobref-index t 1))))))
(define taker
  (lambda ()
    (let ((s (the (blobref blob (arrayof f64 finite)) (blobref-at (the blob (make-bloblet 16)) 0))))
      (reader-for s))))
