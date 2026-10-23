; Verified
;;; A parameter written as a type applied, `(nat 3)`, is not a name: the
;;; specification speaks of the named ones only, and shows the others
;;; unnamed.
(define plus3 (subr pure ((nat 3) (d int)) int (ensures r (= r (+ d 3))))
  (lambda (k d) (+ k d)))
(plus3 3 4)
