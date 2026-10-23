; Verified
;;; A procedure's specification is in its type, so a parameter's type
;;; carries its contract: calling `f`, `twice` owes `f`'s `requires` and
;;; knows its `ensures`.
(define twice (subr pure ((f (subr pure ((x int)) int (requires (< 0 x)) (ensures r (< x r))))
                          (y int))
                    int
                    (requires (< 0 y))
                    (ensures r (< (+ y 1) r)))
  (lambda (f y) (f (f y))))
(define inc (subr pure ((x int)) int (requires (< 0 x)) (ensures r (< x r)))
  (lambda (x) (+ x 1)))
(twice inc 5)
