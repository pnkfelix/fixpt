;;; A procedure that calls one it is given is polymorphic in its effect:
;;; used with one that reads a global, the call reads it.
(define limit int 10)
(define* below (subr pure (int) bool) (lambda (x) (< x limit)))
(define twice (poly ((e effect)) (subr e ((subr e (int) bool) int) bool))
  (plambda ((e effect)) (lambda (f x) (if (f x) (f (+ x 1)) #f))))
((proj twice (read (globals limit))) below 3)
((proj twice pure) (lambda (x) (= x 3)) 3)
