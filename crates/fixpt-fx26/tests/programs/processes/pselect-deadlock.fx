;; ! a deadlock
;; A `pselect` whose cells no task is left to fill: an error, not a hang.
(define a (icell int @c) (make-icell))
(define b (icell int @c) (make-icell))
(pselect ((icell-get a) x x) ((icell-get b) y y))
