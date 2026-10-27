;; A module of each kind of name, one hidden, for `top-include/*.fx`.
(define-generative t int)
(define-type pair-of-t (pairof t t @heap))
(define-effect touches (read @heap))
(hide (define secret int 41))
(define zero t (up-t secret))
(define value (subr pure (t) int) (lambda (v) (+ 1 (down-t v))))
(define both (subr (alloc @heap) (t) pair-of-t) (lambda (v) (cons v v)))
