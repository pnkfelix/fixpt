;; => 18
;; The macro system's spike (`docs/research/datatype-macro.md`): a
;; datatype as a macro, each variant's type chosen by its arity by a macro
;; that makes a description, its values constructed by keywords.
(define-syntax payload
  (-> (type ...) type)
  (syntax-rules ()
    ((_) unit)
    ((_ f) f)
    ((_ f g ...) (tupleof f g ...))))
(define-syntax define-data
  (-> (dvar (label type ...) ...) defn)
  (syntax-rules ()
    ((_ name (t field ...) ...) (define-type name (sumof (t (payload field ...)) ...)))))
(define-data shape (#:circle int) (#:rect int int) (#:none))
(define area (subr pure (shape) int)
  (lambda (s) (tagcase s (#:circle r (* 3 r)) (#:rect (w h) (* w h)) (#:none u 0))))
(+ (area (#:circle 2)) (+ (area (#:rect 3 4)) (area (#:none))))
