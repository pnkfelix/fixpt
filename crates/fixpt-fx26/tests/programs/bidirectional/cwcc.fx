; PLDI '89's C3 without projections. `+` wants an int, which fixes `cwcc`'s
; `t`; its region, which nothing names, is a fresh one, so the control
; effects are masked; its effect binder is the `lambda`'s latent effect.
(+ (cwcc (lambda (f) (f 0))) 1)
