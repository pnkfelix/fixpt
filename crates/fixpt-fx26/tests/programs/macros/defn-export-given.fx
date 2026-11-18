;; ! what a use defines is said in what it makes, `(macro/addressed σ (defn (ℓ δ) …))`, not by `(export σ (rho (ℓ δ) …))` around its parts
;; Herman's form as it once was written, `(export σ (rho …))` around the
;; parts and `defn`, is taken out (TODO.md §288): what a use defines is said
;; in what it makes, `(macro/addressed (bvar expr) (defn ((path #:a) var)))`.
(define-syntax define-const
  (macro/addressed (export (bvar expr) (rho ((path #:a) var))) defn)
  (syntax-rules
    ((_ n e) (define n e))))
(define-const four 4)
four
