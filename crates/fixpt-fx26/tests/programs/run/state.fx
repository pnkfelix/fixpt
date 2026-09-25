; A reference cell: the mutators return the unit value, and reading back
; sees the write.
(define c (ref int @c) (new 1))
(set c 41)
(+ (get c) 1)
