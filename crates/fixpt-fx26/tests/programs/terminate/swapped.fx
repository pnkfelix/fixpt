;;; Two parameters trading places, one counting down: size-change graphs
;;; composed show `a` falling on every second call.
(define* f (subr pure (int int) int) (lambda (a b) (if (> a 0) (f b (- a 1)) 0)))
(f 5 100)
