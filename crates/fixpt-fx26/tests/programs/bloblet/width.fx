;; => 46
;; A bloblet type lists at least its fields (`TODO.md` §77): one of more
;; fields is taken where one of fewer is wanted, since fields count from
;; the suffix, so each keeps its offset. What is forgotten here, a `bool`,
;; an `int` of the heap's own and a ref into the bloblet's own region, no
;; analysis of the wider type needed.
(define-type one (bloblet (fields int) @b))
(define first (subr (read @b) (one) int) (lambda (b) (bloblet-ref b 0)))
(define two (bloblet (fields int bool) @b) (make-bloblet 0 40 #t))
(define three (bloblet (fields int (ref int @b) (listof int acyclic)) @b)
  (make-bloblet 8 5 (new 1) (list 1 2)))
(+ (first two) (+ (first three) (get (bloblet-ref three 1))))
