;; => 3
;; A closure over two modules of one type, each opened by a `let`, and a
;; value of each's: inside, each is the module that value's type names
;; (TAL's unpack: the closure's word is certified so, `free_claims`), which
;; whoever makes the closure must show of each value it gives
;; (`a_closure_over_another_module_of_its_type_is_refused`).
(define-type sig (moduleof (abs t type) (val z t) (val get (subr pure (t) int))))
(define make (subr pure (int) sig)
  (lambda (n)
    (module (define-generative t int #:seal up #:unseal down)
            (define z t (up n))
            (define get (subr pure (t) int) (lambda (c) (down c))))))
(define r
  (let ((p (make 1)) (q (make 2)))
    (let ((x (with p z)) (y (with q z)))
      (lambda () (+ ((with p get) x) ((with q get) y))))))
(r)
