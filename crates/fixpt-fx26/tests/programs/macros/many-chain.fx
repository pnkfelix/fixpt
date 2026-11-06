;; => (7 7)
;; Through another macro's `many` part, a pattern variable said `many` too:
;; the opt-out is in every signature on the way.
(define-syntax both
  ((many expr))
  ((_ e) (list e e)))
(define-syntax both-again
  ((many expr))
  ((_ e) (both e)))
(both-again (+ 3 4))
