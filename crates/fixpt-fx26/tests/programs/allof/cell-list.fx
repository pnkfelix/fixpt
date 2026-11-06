;; ! whose results have no meet
;; A writable list: no two that differ meet (`docs/research/logical-types.md` §8.5,
;; rule 4), as one would be a cell of both types.
;; `ab` and `ac` share the tag `a`: `(sum a 1)` is both.
(define-type ab (sumof (a int) (b int)))
(define-type ac (sumof (a int) (c int)))
(define mk (allof (subr (alloc @h) () (listof ab @h)) (subr (alloc @h) () (listof ac @h)))
  (lambda () (list (sum a 1))))
(let ((v (mk))) (begin (set-car! v (sum b 2)) (tagcase (car v) (a i i) (c k k))))
