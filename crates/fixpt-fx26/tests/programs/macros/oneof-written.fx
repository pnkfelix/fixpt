;; => 3
;; A signature's choice within one operand written `oneof`, as FX-26 names
;; a union of members told apart (`union` read as it too).
(define-syntax opt (oneof () (expr))
  (syntax-rules ((_) 0) ((_ e) e)))
(+ (opt) (opt 3))
