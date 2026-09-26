;;; The suffix: four bytes, written and summed.
(define b (bloblet (fields) @buf) (make-bloblet 4))
(bloblet-set-byte! b 1 200)
(bloblet-set-byte! b 3 55)
(+ (bloblet-bytes b) (+ (bloblet-byte b 1) (bloblet-byte b 3)))
