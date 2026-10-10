;; ! a int is expected here, and this is a m..t
;; A module's abstract type taken in by an `include` stays abstract outside
;; it (`TODO.md` §69): `m`'s `t`, not `int`.
(define m (module (include (module (define-generative t int) (define z t (up-t 5))))))
(with m (+ z 1))
