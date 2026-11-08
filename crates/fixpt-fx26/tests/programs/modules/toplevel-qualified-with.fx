;; => 5
;; A `with` around it does not give it: the top level's `idx`.
(define-type idx int)
(define a (module (define-type idx bool)))
(with a (the #%toplevel:idx 5))
