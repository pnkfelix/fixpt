;; ! whose results have no meet
;; An I-cell, written once: no two that differ meet (`docs/research/logical-types.md` §8.5,
;; rule 4), as one would be a cell of both types.
;; `ab` and `ac` share the tag `a`: `(sum a 1)` is both.
(define-type ab (sumof (a int) (b int)))
(define-type ac (sumof (a int) (c int)))
(define mk (allof (subr (alloc @h) () (icell ab @h)) (subr (alloc @h) () (icell ac @h)))
  (lambda () (make-icell)))
(let ((v (mk))) (begin (icell-put v (sum b 2)) (tagcase (icell-get v) (a i i) (c k k))))
