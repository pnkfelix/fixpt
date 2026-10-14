;; ! a `pselect` arm is
;; A key's arm waits for `(read-byte)`, which takes nothing.
(define a (icell int @c) (make-icell))
(pselect ((icell-get a) x x) ((read-byte a) y 0))
