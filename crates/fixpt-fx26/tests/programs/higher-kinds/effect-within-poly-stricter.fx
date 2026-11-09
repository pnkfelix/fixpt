;; ! `e` is bound within (read r), and e is not: it has e
;; A `poly` whose effect binder's bound is tighter takes fewer effects, so
;; it is not below one whose bound is looser (TODO.md §226).
(define run (poly ((r region) (e effect (within (read r))))
              (subr (read r) ((subr e () int)) int))
  (plambda ((r region) (e effect (within (read r)))) (lambda (h) (+ (h) 1))))
(define wider (poly ((r region) (e effect (within (maxeff (read r) (write r)))))
                (subr (maxeff (read r) (write r)) ((subr e () int)) int))
  run)
