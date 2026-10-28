; Rejected: data frozen into a place as it is made cannot be written.
(define heap-list (listof int acyclic) (list 1 2 3))
(letrena p (let ((xs (the (listof int (acyclic p)) (rcons p 5 heap-list)))) (set-car! xs 6)))
