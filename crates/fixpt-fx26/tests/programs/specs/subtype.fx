; Verified
;;; Behavioural subtyping: `inc` requires less than `use` asks of the
;;; procedure it is given (`0 < x` where `5 < x` is promised), and ensures
;;; more (`x < r`, which with `5 < x` is `0 < r`), so it fits.
(define inc (subr pure ((x : int)) int (requires (< 0 x)) (ensures r (< x r)))
  (lambda (x) (+ x 1)))
(define use (subr pure ((f : (subr pure ((x : int)) int (requires (< 5 x)) (ensures r (< 0 r)))))
                  int
                  (ensures r (< 0 r)))
  (lambda (f) (f 10)))
(use inc)
