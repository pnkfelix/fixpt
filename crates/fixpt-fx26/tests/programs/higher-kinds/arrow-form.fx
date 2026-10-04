;; ! or `(=> (kind …) kind)`
;; An arrow kind lists what it takes, as a `lambda` lists its parameters:
;; `(=> (type) type)`, not `(=> type type)`.
(define-type bad (poly ((f (=> type type))) int))
