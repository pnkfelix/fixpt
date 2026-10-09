;; A module with state, which making allocates: refused as a file every
;; load of which is one value (`TODO.md` §68).
(define c (ref int @c) (new 0))
