;; => 10
;; A described type matches only the same description.
(define m (module (define-type num int) (define x num 10)))
(define-type nums (moduleof (desc num int) (val x num)))
(define get (subr pure (nums) int) (lambda (n) (with n x)))
(get m)
