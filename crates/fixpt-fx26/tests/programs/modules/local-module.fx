;; => 1
;; A module made and opened inside an expression, its type its own.
(let ((m (module (define-generative t int) (define one t (up-t 1))
                 (define get (subr pure (t) int) (lambda (x) (down-t x))))))
  (with m (get one)))
