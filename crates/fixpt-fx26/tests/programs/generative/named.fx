;;; Conversions named where the type is defined (`docs/research/generative-types.md`
;;; §7): `#:seal` and `#:unseal`, ordinary bindings, and no `up-` or `down-`.
(define-generative meters int #:seal to-meters #:unseal from-meters)
(define d meters (to-meters 5))
(define twice (subr pure (meters) meters) (lambda (m) (to-meters (* 2 (from-meters m)))))
(from-meters (twice d))
