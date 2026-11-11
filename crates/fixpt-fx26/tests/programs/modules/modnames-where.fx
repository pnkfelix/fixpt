;; ! `(modnames …)` names no types: it is written as a `define`'s or `the`'s type, whose value supplies them; here a `moduleof` is needed
;; Where no value supplies the types, a parameter's, a `moduleof` is needed.
(define f (lambda ((m (modnames x))) 1))
