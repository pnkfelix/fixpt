;; => 8
;; A name the use gives, defined by a nested use that says so, in the scope
;; of what comes after it. `define-const`'s says it in Herman's form as it
;; once was written, `(export σ β)` around the parts, read as `(defn …)`.
(define-syntax define-const
  (macro/addressed (export (bvar expr) (rho ((path #:a) var))) defn)
  (syntax-rules
    ((_ n e) (define n e))))
(define-syntax define-and-double
  (macro (_ a @ bvar b @ bvar e @ expr) (defn a b))
  (syntax-rules
    ((_ a b e) (begin (define-const a e) (define b (+ a a))))))
(define-and-double four eight 4)
eight
