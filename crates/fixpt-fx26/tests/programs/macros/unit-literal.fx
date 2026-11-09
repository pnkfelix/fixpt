;; => #u
;; `#u` in a template is unit, a literal, not a name of the top level's.
(define-syntax unless0 (expr expr) (syntax-rules () ((_ c body) (if c #u body))))
(unless0 (null? (quote ())) #u)
