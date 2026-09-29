;;; `apply` of a list made cyclic: an error, as Racket's `apply` makes it,
;;; not a loop (`apply` says no `spin`).
(define xs (listof int @heap) (cons 1 (cons 2 nil)))
(set-cdr! (cdr xs) xs)
(the (listof int acyclic) (apply list xs))
