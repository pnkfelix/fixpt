; Rejected: `rnew`'s binder is a place, and a region that is not one cannot
; be given for it.
(letregion r (get ((proj (proj rnew r) int) 0 1)))
