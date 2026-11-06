;; ! whose results have no meet
;; A continuation mark key, whose marks are of its type: no two that differ
;; meet (`docs/research/logical-types.md` §8.5, rule 4), as one would be a
;; cell of both types.
;; `ab` and `ac` share the tag `a`: `(sum a 1)` is both.
(define-type ab (sumof (a int) (b int)))
(define-type ac (sumof (a int) (c int)))
(define mk (allof (subr (alloc @h) () (mark-key ab @h)) (subr (alloc @h) () (mark-key ac @h)))
  (lambda () (make-continuation-mark-key)))
(mk)
