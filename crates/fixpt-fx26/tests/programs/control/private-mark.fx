; A mark key made here and never let out: writing a mark with it and
; reading the mark back cannot be seen from outside, so they are masked,
; as a private cell's reads and writes are.
(let ((key ((proj (proj make-continuation-mark-key @m) int))))
  ((proj (proj with-mark @m) int int (read @m))
   key 1
   (lambda () ((proj (proj first-mark @m) int) key 0))))
