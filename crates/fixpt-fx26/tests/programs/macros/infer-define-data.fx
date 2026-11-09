;; => 18
;; `define-data` with constructor procedures, each signature inferred: a
;; description's macro by its `tupleof`, the definitions' by `begin`.
(define-syntax payload
  (syntax-rules ()
    ((_) unit)
    ((_ f) f)
    ((_ f g ...) (tupleof f g ...))))
(define-syntax define-data
  (syntax-rules ()
    ((_ name (c t field ...) ...)
     (begin
       (define-type name (sumof (t (payload field ...)) ...))
       (define c (subr pure (field ...) name) (lambda ((x field) ...) (t x ...)))
       ...))))
(define-data shape (circle #:circle int) (rect #:rect int int) (none #:none))
(define area (subr pure (shape) int)
  (lambda (s) (tagcase s (#:circle r (* 3 r)) (#:rect (w h) (* w h)) (#:none u 0))))
(+ (area (circle 2)) (+ (area (rect 3 4)) (area (none))))
