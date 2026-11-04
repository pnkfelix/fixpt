;; => (7 7 9)
;; A module reshaped where a call's argument is checked twice (`list`'s, as it
;; is instantiated and then called): reshaped once, not its reshape again (kayak's
;; docs/requests/fixpt-reshape-in-list.md). `m` has a value more than `ab` and
;; `n` its two in the other order; `(extend m n)`'s reshape is made onto `extend`'s.
(define-type ab (moduleof (val b int) (val a int)))
(define m (module (define a int 2) (define c int 4) (define b int 7)))
(define n (module (define a int 2) (define b int 7)))
(define first-b (subr pure (ab) int) (lambda (x) (with x b)))
(define o (module (define b int 9)))
(list (first-b m) (first-b n) (first-b (extend m o)))
