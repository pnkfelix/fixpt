;; ! a one is expected here, and this is a (bloblet (fields int (subr pure () int)) @b)
;; Refused: a forgotten field that holds a procedure, which a knot through
;; the store could be tied with, unseen by the wider type.
(define-type one (bloblet (fields int) @b))
(define b (bloblet (fields int (subr pure () int)) @b) (make-bloblet 0 1 (lambda () 2)))
(define c one b)
