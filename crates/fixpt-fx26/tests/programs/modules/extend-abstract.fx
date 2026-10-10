;; ! `extend` takes a module with abstract types by its name
;; A module's abstract types in an `extend` are the bound module's, `m..t`,
;; aliased (`TODO.md` §69); a module not bound to a name has no such names:
;; refused.
(define b (module (define x int 1)))
(extend (module (define-generative t int) (define y int 2)) b)
