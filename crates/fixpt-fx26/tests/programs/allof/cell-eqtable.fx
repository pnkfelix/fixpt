;; ! whose results have no meet
;; An identity table, whose values are of its type: no two that differ meet.
;; `ab` and `ac` share the tag `a`: `(sum a 1)` is both.
(define-type ab (sumof (a int) (b int)))
(define-type ac (sumof (a int) (c int)))
(define mk (allof (subr (alloc @t) () (eqtable (ref int @k) ab @k @t))
                  (subr (alloc @t) () (eqtable (ref int @k) ac @k @t)))
  (lambda () (make-eqtable (ref-identity))))
(mk)
