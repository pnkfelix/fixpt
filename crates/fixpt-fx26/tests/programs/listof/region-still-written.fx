;; ! a (listof int acyclic) is expected here
;; A list in a region of its own is not acyclic: the default is only for
;; the region left out.
(define-type ints (listof int @heap))
(define xs ints (list 1 2))
(the (listof int) xs)
