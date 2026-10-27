; Refused
;;; A procedure of no specification ensures nothing, so it does not fit
;;; where one that ensures something is expected.
(define inc (subr pure ((x : int)) int)
  (lambda (x) (+ x 1)))
(define use (subr pure ((f : (subr pure ((x : int)) int (ensures r (< x r))))) int)
  (lambda (f) (f 10)))
(use inc)
