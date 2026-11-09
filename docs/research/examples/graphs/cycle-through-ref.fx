;;; A cycle through frozen data needs a recursive type through writable
;;; storage: here `cell`, a ref whose contents are acyclic lists of cells.
;;; The list is frozen, but the ref it holds is not, and writing the list
;;; into the ref closes c -> l -> c (graphs.md §2.7).
(define-type cell (ref (listof cell acyclic) @r))
(define c cell (new (the (listof cell acyclic) (list))))
(define l (listof cell acyclic) (list c))
(set c l)
;; c -> l -> c: from c, through the list and the ref twice, back to c.
(eq? c (car (get (car (get c)))))
