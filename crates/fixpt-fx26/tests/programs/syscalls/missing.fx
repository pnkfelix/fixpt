;;; A required syscall this runtime has not: its declaration fails as it
;;; loads, naming it.
(define-syscall frob "test:frob/1" (subr (io sys) (int) int))
