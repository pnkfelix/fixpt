;; ! a one is expected here, and this is a (bloblet (fields int (ref int @heap)) @b)
;; Refused: a forgotten field's ref into the heap, from a bloblet not of the
;; heap: storage the wider type would not say it has.
(define-type one (bloblet (fields int) @b))
(define r (ref int @heap) (new 1))
(define b (bloblet (fields int (ref int @heap)) @b) (make-bloblet 0 1 r))
(define c one b)
