;; => 8
;; A name the use gives, defined by a nested use that says so, in the scope
;; of what comes after it. `define-const`'s says it as it once was, `(export
;; σ β)` around the parts, which is read as `(defn …)` is.
(define-syntax define-const
  (-> (export (bvar expr) (rho (A var))) defn)
  (syntax-rules
    ((_ n e) (define n e))))
(define-syntax define-and-double
  (-> (bvar bvar expr) (defn (A var) (AD var)))
  (syntax-rules
    ((_ a b e) (begin (define-const a e) (define b (+ a a))))))
(define-and-double four eight 4)
eight
