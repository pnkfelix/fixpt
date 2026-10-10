;; ! `v`'s type mentions `t`, which is hidden in this module
;; A hidden abstract type in a type shown is refused, for now (the user's,
;; 2026-10-09: safe while the feature is tried; abstract, later, perhaps).
(define m (module (hide (define-generative t int)) (define v t (up-t 1))))
