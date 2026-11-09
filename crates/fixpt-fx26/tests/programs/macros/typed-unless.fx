;; => #u
;; A macro whose parts are typed (`typed-macros.md`, "Proposed: typed
;; holes"): its template checked once, where it is defined, as a procedure
;; over its holes; polymorphic in the body's effect.
(define-syntax unless
  (poly ((e effect))
    ((expr #:type bool #:effect pure) (expr #:type unit #:effect e)))
  (syntax-rules ()
    ((_ c body) (if c #u body))))
(unless (null? '()) #u)
