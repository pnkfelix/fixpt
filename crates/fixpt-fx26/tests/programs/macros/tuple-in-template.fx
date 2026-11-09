;; => 12
;; A template's `tuple`, and a keyword constructing in a template, written
;; or a pattern variable's.
(define-syntax point
  (expr expr)
  (syntax-rules ()
    ((_ a b) (#:pt (tuple a b)))))
(define-syntax tagged
  (label expr)
  (syntax-rules ()
    ((_ t e) (t e))))
(define-type p (sumof (#:pt (tupleof int int))))
(define area (subr pure (p) int) (lambda (s) (tagcase s (#:pt (x y) (* x y)))))
(+ (area (point 2 3)) (area (tagged #:pt (tuple 3 2))))
