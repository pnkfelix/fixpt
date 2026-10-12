;; => (5 3 5)
;; `blobref-length` (TODO.md §77, N5c): a flat array's length, a `(nat n)`
;; of its length `n`. Of an array that runs to the end of the suffix, the
;; whole elements left there (44 bytes, five `f64`s); of a literal one, its
;; literal. A test of an index against it teaches `i < n`, so the index in
;; `total` is shown in bounds (`NodeFacts::in_bounds`).
(define-type blob (bloblet (fields) @heap))
(define* total
  (poly ((n size)) (subr (maxeff (read @heap) spin) ((blobref blob (arrayof f64 n)) nat f64) f64))
  (plambda ((n size))
    (lambda (s i acc)
      (if (< i (blobref-length s))
          ((proj total n) s (+ i 1) (f64+ acc (blobref-get (blobref-index s i))))
          acc))))
(define main
  (subr (maxeff (alloc @heap) (read @heap) (write @heap) spin (read (globals total)))
        ()
        (listof int acyclic))
  (lambda ()
    (let* ((b (the blob (make-bloblet 44)))
           (s (the (blobref blob (arrayof f64 finite)) (blobref-at b 0)))
           (t (the (blobref blob (arrayof f64 3)) (blobref-at b 0))))
      (begin (blobref-set! (blobref-index s 4) 2.5)
             (list (blobref-length s) (blobref-length t) (f64->int (f64* 2. (total s 0 0.))))))))
(main)
