; The same with `key : (mark-key int @m)` bound by the test: the key is
; shared, so the write and the read stay.
((proj (proj with-mark @m) int int (read @m))
 key 1
 (lambda () ((proj (proj first-mark @m) int) key 0)))
