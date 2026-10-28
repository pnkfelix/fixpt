; Rejected: data frozen into a place may not leave the place.
(define heap-list (listof int acyclic) (list 1 2 3))
(letrena p (the (listof int (acyclic p)) (rcons p 5 heap-list)))
