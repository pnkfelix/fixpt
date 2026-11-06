;; ! whose results are procedures that may keep what the call allocates: one value would be both
;; A cell smuggled out through a closure's free variable. Under each member
;; the cell's contents are typed by the parameter, `ab` under one and `ac`
;; under the other; one call fitting both makes one cell, and the meet of
;; the results (an `allof` of the two closures) would keep both views of it
;; (`docs/research/logical-types.md` §8.5, rule 4's fresh regions). Before
;; the rule this ran, and printed 202: the `c` arm, for a `b`.
;; `ab` and `ac` share the tag `a`: `(sum a 1)` is both.
(define-type ab (sumof (a int) (b int)))
(define-type ac (sumof (a int) (c int)))
(define mk (allof (subr (alloc @h) (ab) (subr pure () (ref ab @h)))
                  (subr (alloc @h) (ac) (subr pure () (ref ac @h))))
  (lambda (x) (let ((c ((proj new @h) x))) (lambda () c))))
(define g (mk (sum a 1)))
;; What it would have allowed: write a `b` as an `ab`, read it as an `ac`.
(define as-ab (subr pure () (ref ab @h)) g)
(define as-ac (subr pure () (ref ac @h)) g)
(set (as-ab) (sum b 2))
(tagcase (get (as-ac)) (a i (+ i 100)) (c k (+ k 200)))
