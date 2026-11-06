;; ! whose results have no meet
;; Refs in a frozen list: no two that differ meet (`docs/research/logical-types.md` §8.5,
;; rule 4), as one would be a cell of both types.
;; `ab` and `ac` share the tag `a`: `(sum a 1)` is both.
(define-type ab (sumof (a int) (b int)))
(define-type ac (sumof (a int) (c int)))
(define mk (allof (subr (alloc @h) () (listof (ref ab @h) acyclic))
                  (subr (alloc @h) () (listof (ref ac @h) acyclic)))
  (lambda () (list ((proj new @h) (sum a 1)))))
(let ((v (car (mk)))) (begin (set v (sum b 2)) (tagcase (get v) (a i i) (c k k))))
