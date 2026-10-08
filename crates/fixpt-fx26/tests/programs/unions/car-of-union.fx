;;; `car` and `cdr` of a union with a pair member (a `datum`, say) take that
;;; member apart, as they take apart a pair that may be `nil`: every machine
;;; checks that the argument is a pair, and traps if not.
(define d datum (list 1 'a 2))
(define* num (subr pure (datum) int)
  (lambda (x) (typecase x (int i i) (else e 0))))
(+ (num (car d)) (num (car (cdr (cdr d)))))
