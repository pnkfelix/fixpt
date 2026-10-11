;; ! which flat a new `blobref` points to is said by the type it is checked against
;; A new blobref's flat is the type it is checked against's.
(define-type pt (bloblet (fields int) @b))
(define b pt (make-bloblet 24 7))
(blobref-get (blobref-at b 0))
