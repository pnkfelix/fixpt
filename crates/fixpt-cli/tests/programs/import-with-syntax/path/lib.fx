;; A file with a module parameter, whose macros' templates name a type its
;; parameter gives it, and a value it hides (Heist's report, 2026-11-18).
(module-parameters ((m-base (load-moduleof "base.fx"))))
(hide (define offset int 10))
(define-syntax make-thing (macro (_ e @ expr) expr) (syntax-rules ((_ e) (the thing e))))
(define-syntax plus-offset (macro (_ e @ expr) expr) (syntax-rules ((_ e) (+ e offset))))
(define zero (make-thing (product (n 0))))
