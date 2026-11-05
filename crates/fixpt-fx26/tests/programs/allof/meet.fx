;; => (1 2 3)
;; A call takes every member it fits, its result the meet of theirs: an
;; `(sumof (a int))` fits both, and is what the call gives, which `only-a`
;; takes; a member alone where a `subr` is expected, by subtyping.
(define-type ab (sumof (a int) (b int)))
(define-type ac (sumof (a int) (c int)))
(define f (allof (subr pure (ab) ab) (subr pure (ac) ac)) (lambda (s) s))
(define only-a (subr pure ((sumof (a int))) int) (lambda (s) (tagcase s (a i i))))
(define apply-ab (subr pure ((subr pure (ab) ab) ab) int)
  (lambda (g s) (tagcase (g s) (a i i) (b j j))))
(list (only-a (f (sum a 1))) (apply-ab f (sum b 2)) (tagcase (f (sum c 3)) (a i i) (c k k)))
