;; ! this macro's expansion does not end: 10000 uses expanded in one form, the last of `t`, inside `t`, `t`, `t`, `t`
;; A finite expansion too large to make: uses side by side, each making two
;; more, 14 deep, 32767 in all; none is one it came from (its siblings are
;; the same, and are not around it), and none deep.
(define-syntax t (syntax-rules ((_ ()) 1) ((_ (x . r)) (+ (t r) (t r)))))
(t (a a a a a a a a a a a a a a))
