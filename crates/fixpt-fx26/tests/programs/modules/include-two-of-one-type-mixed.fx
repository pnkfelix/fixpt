;; ! argument 1 is a q..t, where a p..t is expected
;; Two modules of one type, included as members, are two modules
;; (`TODO.md` §308): the include's `with` opens each, `p` and `q`, at
;; its own types, so `p`'s procedure is given no value of `q`'s.
(define-type sig (moduleof (abs t type) (val z t) (val get (subr pure (t) int))))
(define make (subr pure (int) sig)
  (lambda (n)
    (module (define-generative t int #:seal up #:unseal down)
            (define z t (up n))
            (define get (subr pure (t) int) (lambda (c) (down c))))))
(define make2 (subr (read (globals make)) () (moduleof (val p sig) (val q sig)))
  (lambda () (module (define p (make 1)) (define q (make 2)))))
(define m (module (include (make2))
                  (define x ((with p get) (with q z)))
                  (define y ((with q get) (with q z)))))
(+ (with m x) (with m y))
