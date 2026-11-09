;; ! `x` is bound in a use of `define-const`, whose signature does not say its uses define it
;; What a nested use defines unsaid by its signature: refused, not read at
;; the top level, which the template would seem to mean.
(define-syntax define-const
  (-> (bvar expr) defn)
  (syntax-rules ()
    ((_ n e) (define n e))))
(define-syntax define-via
  (-> (bvar) defn)
  (syntax-rules ()
    ((_ name) (begin (define-const x 1) (define name x)))))
