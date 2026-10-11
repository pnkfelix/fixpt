;;; `length` of a list at `acyclic`, which is a `nlist` of some length
;;; (`(listof T acyclic)` and `(nlist T finite)` are each other's subtypes).
(define l (listof int acyclic) (list 1 2))
(length l)
