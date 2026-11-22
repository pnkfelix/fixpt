;; => 3
;; Two modules of one type, `sig`, made by one maker and included as a
;; module's members: each its own abstract type, a value of one not given
;; to the other's procedure (the cell verifier's, `TODO.md` §307: each read
;; of either opened apart, the two binding one variable).
(define-type sig (moduleof (abs t type) (val z t) (val get (subr pure (t) int))))
(define make (subr pure (int) sig)
  (lambda (n)
    (module (define-generative t int #:seal up #:unseal down)
            (define z t (up n))
            (define get (subr pure (t) int) (lambda (c) (down c))))))
(define make2 (subr (read (globals make)) () (moduleof (val p sig) (val q sig)))
  (lambda () (module (define p (make 1)) (define q (make 2)))))
(define m (module (include (make2))
                  (define x ((with p get) (with p z)))
                  (define y ((with q get) (with q z)))))
(+ (with m x) (with m y))
