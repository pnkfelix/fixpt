;; ! whose results have no meet
;; An array: no two that differ meet (`docs/research/logical-types.md` §8.5,
;; rule 4), as one would be a cell of both types.
;; `ab` and `ac` share the tag `a`: `(sum a 1)` is both.
(define-type ab (sumof (a int) (b int)))
(define-type ac (sumof (a int) (c int)))
(define mk (allof (subr (alloc @h) () (arrayof ab @h)) (subr (alloc @h) () (arrayof ac @h)))
  (lambda () (make-array 1 (sum a 1))))
(let ((v (mk))) (begin (array-set! v 0 (sum b 2)) (tagcase (array-ref v 0) (a i i) (c k k))))
