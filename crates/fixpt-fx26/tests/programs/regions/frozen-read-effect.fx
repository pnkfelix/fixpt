; Rejected: reading data frozen into arena `a` is an effect on it, so a
; closure that does is not `pure` while `a` is seen (docs/research/
; soundness-findings.md, F2); the place's end masks it, as in
; run/letfreeze-into-place.fx.
(define total (subr pure (int) int)
  (lambda (n)
    (letrena a
      (let ((xs (letfreeze (r a) (the (listof int r) (rcons a n (rcons a 2 nil))))))
        (let ((f (the (subr pure () int) (lambda () (car xs)))))
          (f))))))
