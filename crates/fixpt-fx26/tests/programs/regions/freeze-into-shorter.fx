; Rejected: data frozen into `a` must be in `a`, or a place outliving it; `b`
; ends first, so `rcons` may not put the data there.
(letrena a
  (letrena b
    (car (letfreeze (r a) (the (listof int r) (rcons b 1 nil))))))
