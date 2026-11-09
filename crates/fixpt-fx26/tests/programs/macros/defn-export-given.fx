;; => 8
;; A name the use gives, defined by a nested use that says so, in the scope
;; of what comes after it.
(define-syntax define-const
  (-> (export (bvar expr) (rho (A var))) defn)
  (syntax-rules ()
    ((_ n e) (define n e))))
(define-syntax define-and-double
  (-> (export (bvar bvar expr) (rho (A var) (AD var))) defn)
  (syntax-rules ()
    ((_ a b e) (begin (define-const a e) (define b (+ a a))))))
(define-and-double four eight 4)
eight
