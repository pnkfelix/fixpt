;; => 5
;; A template's `letregion`, its region made fresh in its types.
(define-syntax in-region (expr)
  (syntax-rules ()
    ((_ e) (letregion r ((the (subr pure ((listof int r)) int) (lambda (xs) e)) nil)))))
(in-region 5)
