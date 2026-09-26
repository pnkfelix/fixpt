;;; FX-91's define-datatype: a recursive sum of products, taken apart by
;;; tagcase, whose arms name each variant's members.
(define-datatype expr (num int) (add expr expr) (neg expr))
(define value (subr pure (expr) int)
  (lambda (e)
    (tagcase e
      (num (n) n)
      (add (a b) (+ (value a) (value b)))
      (neg (x) (- 0 (value x))))))
(value (add (num 30) (add (neg (num 1)) (num 13))))
