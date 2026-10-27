; Refused
;;; The result is named by a name.
(define f (subr pure ((x : int)) int (ensures (r) (< 0 r))) (lambda (x) x))
