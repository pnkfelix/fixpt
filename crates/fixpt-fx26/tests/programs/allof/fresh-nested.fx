;; ! whose results are procedures that may keep what the call allocates: one value would be both
;; A procedure that makes a fresh cell each call is no smuggling, but the
;; meet of the two is refused where they are made (they name the region the
;; call allocates in); before the rule, only the inner call was.
;; `ab` and `ac` share the tag `a`: `(sum a 1)` is both.
(define-type ab (sumof (a int) (b int)))
(define-type ac (sumof (a int) (c int)))
(define mk (allof (subr (alloc @h) () (subr (alloc @h) () (ref ab @h)))
                  (subr (alloc @h) () (subr (alloc @h) () (ref ac @h))))
  (lambda () (lambda () ((proj new @h) (sum a 1)))))
(mk)
