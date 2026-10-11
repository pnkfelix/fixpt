; Accepted: F17's self-application through `app` (docs/research/
; soundness-findings.md), its loop said: `T` and `omega` say `spin`. And a
; polymorphic value given no procedure (`cons`, an identity) is as pure at a
; cyclic type as at any other.
(define-type T (subr spin (T) int))
(define omega (subr spin () int)
  (lambda ()
    (let ((app (the (poly ((t type)) (subr spin ((subr spin (t) int) t) int))
                    (plambda ((t type)) (lambda ((f (subr spin (t) int)) (x t)) (f x))))))
      (let ((w (the T (lambda (x) ((proj app T) x x)))))
        ((proj app T) w w)))))
(define kept (subr pure (T) (listof T acyclic))
  (lambda (w)
    (let ((id (the (poly ((t type)) (subr pure (t) t)) (plambda ((t type)) (lambda ((x t)) x)))))
      (cons ((proj id T) w) nil))))
; What it returns returns itself: each such procedure, at any depth, says
; `spin`, a cycle made a cycle.
(define-type S (subr pure () S))
(define-type S-spin (subr spin () S-spin))
(define app-s (poly ((t type)) (subr pure ((subr pure (t) int) t S) S))
  (plambda ((t type)) (lambda ((f (subr pure (t) int)) (x t) (s S)) s)))
(define app-s-at-T
  (subr (read (globals app-s)) () (subr spin ((subr pure (T) int) T S) S-spin))
  (lambda () (proj app-s T)))
