; Rejected: the heap's frozen data cannot be a place's, which ends first.
(define heap-list (listof int acyclic) (list 1 2 3))
(letrena p (let ((xs (the (listof int (acyclic p)) (rcons p 5 heap-list))))
             (length (the (listof int acyclic) xs))))
