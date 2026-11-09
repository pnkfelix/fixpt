;; => 1
;; An ellipsis in a template's description: a tuple of the types a use
;; gives.
(define-syntax as-tuple
  (expr type ...)
  (syntax-rules ()
    ((_ e t ...) (the (tupleof t ...) e))))
(extract (as-tuple (tuple 1 #t) int bool) 1)
