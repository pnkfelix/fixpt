; Rejected: an inner place's frozen data cannot be an outer place's.
(define heap-list (listof int acyclic) (list 1 2 3))
(letrena p
  (letrena q
    (let ((inner (the (listof int (acyclic q)) (rcons q 2 heap-list))))
      (let ((outer (the (listof int (acyclic p)) (rcons p 1 inner)))) 0))))
