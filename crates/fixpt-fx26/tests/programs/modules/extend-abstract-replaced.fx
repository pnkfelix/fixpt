;; ! `zero`'s type mentions the first module's `t`, which the second's `t` replaces
;; `e1`'s names replace `e0`'s in an `extend`, abstract types too; one of
;; `e0`'s own that a value kept still mentions would be left without a name
;; (`TODO.md` §69): refused.
(extend (module (define-generative t int) (define zero t (up-t 0)))
        (module (define-generative t bool)))
