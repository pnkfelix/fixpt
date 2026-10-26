;;; A required syscall this runtime has at another type: its declaration
;;; fails as it loads, saying both, each in canonical form: names expanded,
;;; effects sorted and each once, region binders `r1`, `r2` in order.
(define-type (words (r region)) (flatarrayof i64 r))
(define-effect sys (io sys))
(define-syscall flush-code "code:flush/1"
  (poly ((zeta region) (alpha region))
    (subr (maxeff (write alpha) sys (read zeta) (read zeta))
          ((words zeta) (words alpha) int) unit)))
