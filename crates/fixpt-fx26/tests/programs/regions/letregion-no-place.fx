; Rejected: a `letregion` makes no place, so its name is no value, and there
; is nothing for `rcons` to allocate in.
(letregion r (car (the (listof int r) (rcons r 1 nil))))
