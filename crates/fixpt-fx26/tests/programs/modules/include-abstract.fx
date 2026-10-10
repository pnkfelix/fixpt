;; ! `include` takes a module with abstract types by its name
;; A module's abstract types in an `include` are the bound module's, `m..t`,
;; aliased (`TODO.md` §69); a module not bound to a name has no such names:
;; refused.
(module (include (module (define-generative t int) (define v t (up-t 1)))))
