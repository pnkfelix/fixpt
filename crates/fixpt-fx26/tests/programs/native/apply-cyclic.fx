;;; `apply` of a list made cyclic: an error, as Racket's `apply` makes it,
;;; not a loop (`apply` says no `spin`).
(define xs (listof int @heap) (list 1 2))
(set-cdr! (cdr xs) xs)
(the (listof int acyclic) (apply list xs))
