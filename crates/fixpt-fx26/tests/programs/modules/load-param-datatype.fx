;; => 7
;; A file whose datatype has a parameter, loaded (`../module-files/option.fx`):
;; both checkers read it, as the same module type (PLAN.md Q13, O15).
(define o (load-module "../module-files/option.fx"))
(with o (tagcase seven (none () 0) (some (x) x)))
