;; ! `v`'s type mentions `t`, which is hidden in this module: show `t`, or hide `v` as well
;; A hidden abstract type in a type shown is refused (the user's,
;; 2026-10-09, kept 2026-11-13: `TODO.md` §69). Shown, it is abstract
;; outside all the same; hidden, it would be a type no one could write.
(define m (module (hide (define-generative t int)) (define v t (up-t 1))))
