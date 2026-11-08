;; => 18
;; A keyword at a list's head constructs a sum: of none, `unit`; of one,
;; the value itself; of more, a tuple of them, taken apart by `tagcase`
;; (`docs/research/datatype-macro.md`, "Keyword constructors: decided").
(define-type shape (sumof (#:circle int) (#:rect (tupleof int int)) (#:none unit)))
(define area (subr pure (shape) int)
  (lambda (s) (tagcase s (#:circle r (* 3 r)) (#:rect (w h) (* w h)) (#:none u 0))))
(+ (area (#:circle 2)) (+ (area (#:rect 3 4)) (area (#:none))))
