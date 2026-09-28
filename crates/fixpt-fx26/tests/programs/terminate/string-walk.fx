;;; Counting up to a bound made from a parameter every call passes on
;;; unchanged: `s` is the same for the whole recursion, so its length is.
(define count-a (subr pure (string int int) int)
  (letrec ((count-a (subr pure (string int int) int)
             (lambda (s i n) (if (< i (string-length s)) (count-a s (+ i 1) (if (char=? (string-ref s i) #\a) (+ n 1) n)) n))))
    count-a))
(count-a "banana" 0 0)
