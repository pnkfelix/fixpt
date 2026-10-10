;; ! `f` and `f'` are different variables, each named `f`
;; The user's okasaki.fx: `the` of a type `poly` over its own `f`, around a
;; module of the `plambda`'s `f`. Two `f`s, primed apart; the modules' own
;; `susp`s are bound by each `moduleof`, and not. Written so it checks, it
;; is `(define mod-lazy-int sig-lazy-int (plambda …))`, no `the`.
(define-type sig-lazy-int
  (poly ((f effect))
    (moduleof
     (abs susp type)
     (val delay (subr (maxeff f (alloc @heap)) ((subr f () int)) susp))
     (val force (subr (maxeff f (read @heap)) (susp) int)))))
(define mod-lazy-int
  (plambda ((f effect))
    (the sig-lazy-int
      (module
        (define-generative susp (ref int @heap))
        (define delay (lambda ((cxn (subr f () int))) (up-susp (new (cxn)))))
        (define force (subr (maxeff f (read @heap)) (susp) int)
          (lambda ((s susp)) (get (down-susp s))))))))
