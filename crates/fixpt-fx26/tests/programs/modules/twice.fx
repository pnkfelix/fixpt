;; ! `t` appears twice
;; A module type names each component once: each type, and each value (a
;; value may have a type's name, `modules/type-and-value.fx`).
(define-type bad (moduleof (abs t type) (desc t int)))
