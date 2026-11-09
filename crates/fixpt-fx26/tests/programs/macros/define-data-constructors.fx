;; => 18
;; `define-data` with constructor procedures beside the keywords, as a
;; datatype's were before keyword constructors: the use names each, and
;; the template defines them, one `define` per variant, by ellipsis in a
;; `begin` (each definition in the scope of those before it); each
;; constructs by its keyword, a pattern variable at a list's head.
(define-syntax payload
  (-> (type ...) type)
  (syntax-rules ()
    ((_) unit)
    ((_ f) f)
    ((_ f g ...) (tupleof f g ...))))
(define-syntax define-data
  (-> (dvar (bvar label type ...) ...) defn)
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
