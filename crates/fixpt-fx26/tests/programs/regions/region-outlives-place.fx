; Rejected: a region bound outside an arena could outlive it, so `rcons`
; may not put its data there.
(letregion outer
  (letrena p
    (car (the (listof int outer) (rcons p 1 nil)))))
