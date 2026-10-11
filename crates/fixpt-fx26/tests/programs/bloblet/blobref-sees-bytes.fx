;; => (1 0 0 0 255 255 255 255)
;; Bytes written through a blobref are the suffix's: an `i32` 1, then -1,
;; as their little-endian bytes.
(define-type pt (bloblet (fields) @b))
(define b pt (make-bloblet 8))
(blobref-set! (the (blobref pt i32) (blobref-at b 0)) 1)
(blobref-set! (the (blobref pt i32) (blobref-at b 4)) -1)
(list (bloblet-byte b 0) (bloblet-byte b 1) (bloblet-byte b 2) (bloblet-byte b 3)
      (bloblet-byte b 4) (bloblet-byte b 5) (bloblet-byte b 6) (bloblet-byte b 7))
