;; ! `include` of a module with abstract types is not supported yet
;; Not yet (`TODO.md` §69), as `extend`.
(module (include (module (define-generative t int) (define v t (up-t 1)))))
