;; => 15
;; A procedure of a blobref to an array that runs to the end of the suffix
;; passes its own parameter on: the length named where the parameter is
;; bound means just what `finite` does there, so it is the type the
;; procedure takes (TODO.md §77). Its index is shown in bounds.
(define-type blob (bloblet (fields) @heap))
(define-type arr (blobref blob (arrayof i64 finite)))
(define* total
  (subr (maxeff (read @heap) spin) (arr nat int) int)
  (lambda (s i acc)
    (if (< i (blobref-length s))
        (total s (+ i 1) (+ acc (i64->int (blobref-get (blobref-index s i)))))
        acc)))
(define b blob (make-bloblet 44))
(define s arr (blobref-at b 0))
(define* fill
  (subr (maxeff (read @heap) (write @heap) spin) (arr nat) unit)
  (lambda (s i)
    (if (< i (blobref-length s))
        (begin (blobref-set! (blobref-index s i) (int->i64 (+ i 1))) (fill s (+ i 1)))
        #u)))
(fill s 0)
(total s 0 0)
