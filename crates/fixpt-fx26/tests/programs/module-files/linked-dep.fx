;; A module a conductor makes once, and passes to those that use it.
(define cat3 (subr pure (string string string) string)
  (lambda (x y z) (string-append x (string-append y z))))
(define limit int 7)
