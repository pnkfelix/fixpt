;; ! a description function parameter is invariant
;; A generative type's type-constructor parameter takes no variance mark.
(define-generative (wrapped (f (=> type type) +) (a type)) (f a))
