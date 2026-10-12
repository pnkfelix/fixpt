; A condition raised with no handler: a panic, the run ends (TODO.md §89).
(define c (load-module "fx26:conditions.fx"))
(define raise (with c raise))
(define k ((proj (proj make-continuation-mark-key @k) (subr pure (int) int))))
((proj (proj raise @k) int int pure) k 5)
