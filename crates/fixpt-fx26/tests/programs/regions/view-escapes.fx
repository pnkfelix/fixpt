; Rejected: a view of a buffer at a region (TODO.md §310) is at that
; region, so a slice of a buffer still written leaves it no more than the
; buffer does: not as a `str`, frozen data.
(define* esc (poly ((r region)) (subr (alloc r) () str))
  (lambda () (str-slice (the (stringof r) (make-string 3 #\x)) 0 2)))
