;;; A pure syscall declared with `(io sys)`: a type other than the
;;; runtime's, so its declaration fails as it loads, as any difference does.
(define-syscall utf8-length "kayak:string-utf8-length/1" (subr (io sys) (string) int))
