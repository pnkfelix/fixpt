; `control/capture-and-resume.fx` without projections. The continuation's
; type is known once the tag is: `call-with-composable-continuation`'s
; binders come from `t`, and the `lambda` is told what `k` is.
(define t (prompt-tag int int (read (globals t)) @p) (make-continuation-prompt-tag))

(prompt t
  (+ 1 (call-with-composable-continuation (lambda (k) (k (k 1))) t))
  (lambda (v) v))
