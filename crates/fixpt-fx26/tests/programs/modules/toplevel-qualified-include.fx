;; ! `u` is not a type
;; The top level's `u`: none, whatever a module's `include`s give where it
;; is written.
(define lib (module (define-type u int)))
(define m (module (include lib) (define x #%toplevel:u 1)))
(with m x)
