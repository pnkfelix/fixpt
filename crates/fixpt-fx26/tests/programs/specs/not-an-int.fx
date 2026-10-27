; Refused
;;; A proposition's integers are `int`s and `nat`s: a string is not one.
(define f (subr pure ((s : string)) int (ensures r (< s r)))
  (lambda (s) 0))
(f "a")
