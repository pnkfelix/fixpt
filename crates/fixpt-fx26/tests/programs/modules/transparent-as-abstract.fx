;; => 6
;; A transparent type where an abstract one is wanted: abstract there.
(define n
  (module (define-type t int)
          (define x t 5)
          (define bump (subr pure (t) t) (lambda (k) (+ k 1)))))
(define-type opaque (moduleof (abs t type) (val x t) (val bump (subr pure (t) t))))
(define get (subr pure (opaque) int) (lambda (m) 6))
(get n)
