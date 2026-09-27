; Rejected: a `const` list may be cyclic, so it has no length.
(define l (listof int const) (letfreeze r (the (listof int r) (cons 1 nil))))
(define v (vec int finite) l)
