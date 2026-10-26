;;; An optional syscall this runtime has not: the program loads, says so,
;;; and a call of it fails.
(define-optional-syscall frob "test:frob/1" (subr (io sys) (int) int))
(syscall-available? frob)
(frob 1)
