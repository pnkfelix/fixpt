;; ! whose results are procedures that may keep what the call allocates: one value would be both
;; The same within a `letregion`, masked outside: `run` would be `pure`, and
;; give 202. The rule looks at the call's own effect, before masking.
;; `ab` and `ac` share the tag `a`: `(sum a 1)` is both.
(define-type ab (sumof (a int) (b int)))
(define-type ac (sumof (a int) (c int)))
(define* run (subr pure () int)
  (lambda ()
    (letregion r
      (let ((mk (the (allof (subr (alloc r) (ab) (subr pure () (ref ab r)))
                            (subr (alloc r) (ac) (subr pure () (ref ac r))))
                  (lambda (x) (let ((c ((proj new r) x))) (lambda () c))))))
        (let* ((g (mk (sum a 1)))
               (as-ab (the (subr pure () (ref ab r)) g))
               (as-ac (the (subr pure () (ref ac r)) g)))
          (begin (set (as-ab) (sum b 2))
                 (tagcase (get (as-ac)) (a i (+ i 100)) (c k (+ k 200)))))))))
(run)
