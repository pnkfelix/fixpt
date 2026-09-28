; `control/own-abort.fx` without a single projection: the tag's type comes
; from the signature, `abort-current-continuation` is instantiated from its
; arguments, and the handler's parameter type from the tag.
(define t (prompt-tag int int (read (globals t)) @p) (make-continuation-prompt-tag))

(prompt t
  (+ 1 (abort-current-continuation t 5))
  (lambda (v) v))
