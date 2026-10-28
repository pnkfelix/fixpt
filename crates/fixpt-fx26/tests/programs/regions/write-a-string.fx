; Rejected: a `string` is `(stringof const)`, frozen, and nothing may
; write it.
(define s string "abc")
(string-set! s 0 #\x)
