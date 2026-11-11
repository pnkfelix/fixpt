;; A file of module parameters that uses macros of its own (Heist's,
;; 2026-11-11): its parameter's `include` is around the macro's definition
;; as around each use, so a free name of the template means at a use what
;; it means where the macro is defined: `one`, the parameter's, even inside
;; a binder `one` of the use's, which is renamed.
(module-parameters ((m-base (load-moduleof "own-macros-base.fx"))))
(define-syntax add-one (syntax-rules () ((_ e) (+ e one))))
(define g (subr pure (int) int) (lambda (n) (add-one n)))
(define h (subr pure (int) int) (lambda (one) (add-one one)))
