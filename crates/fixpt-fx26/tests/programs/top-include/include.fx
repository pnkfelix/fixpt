;; => 42
;; A top-level `include` defines here what a module gives, by name: values,
;; types and effects (the user's, 2026-10-27, Heist's problem F); a type
;; or effect defined after it is read in order, and may name them.
(define m (load-module "../module-files/include-lib.fx"))
(include m)
(define first (subr (read @heap) (pair-of-t) t) (lambda (p) (car p)))
(define-effect mine touches)
(value (first (both zero)))
