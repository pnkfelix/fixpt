;; => (4 4)
;; An argument placed twice is two expressions, each with what the checkers
;; find of it, though both are at one place in the text (its provenance):
;; a `tagcase`, checked and compiled at each copy.
(define-type opt (sumof (some int) (none unit)))
(define-syntax both
  ((many expr))
  ((_ e) (list e e)))
(let ((o (the opt (sum some 4))))
  (both (tagcase o (some v v) (none u 0))))
