; Refused
;;; `inc` requires `0 < x`, more than `use` promises the procedure it is
;;; given (`-5 < x`): it does not fit.
(define inc (subr pure ((x int)) int (requires (< 0 x)) (ensures r (< x r)))
  (lambda (x) (+ x 1)))
(define use (subr pure ((f (subr pure ((x int)) int (requires (< -5 x)) (ensures r (< x r)))))
                  int)
  (lambda (f) (f 10)))
(use inc)
