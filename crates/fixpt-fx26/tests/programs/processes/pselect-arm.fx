;; ! a `pselect` arm is
;; An arm waits for an I-cell or a mailbox, and names what it gets.
(define a (icell int @c) (make-icell))
(pselect ((icell-get a) x x) ((get a) y y))
