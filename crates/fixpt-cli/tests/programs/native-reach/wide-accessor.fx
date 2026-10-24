;;; An accessor of a record of more fields than a leaf has registers: its
;;; `tagcase` loads only the field it uses (`native_reach.rs`).
(define-datatype big (big int int int int int int int int int))
(define big-8 (subr pure (big) int) (lambda (v) (tagcase v (big (a b c d e f g h i) h))))
(big-8 (big 1 2 3 4 5 6 7 8 9))
