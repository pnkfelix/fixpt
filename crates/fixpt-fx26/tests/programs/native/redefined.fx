;;; A global redefined after native code bound it as compiled: that code
;;; sees the new definition, as every other machine's does. `rd-old` keeps
;;; the first `rd-f`, whose recursive call is the global's; `rd-old-g` the
;;; first `rd-g`, which passes the global `rd-g` as a value.
(define* rd-f (subr spin (int) int) (lambda (x) (if (= x 0) 0 (+ 1 (rd-f (- x 1))))))
(define rd-old (subr (maxeff spin (read (globals rd-f))) (int) int) rd-f)
(rd-old 3)
(define* rd-f (subr spin (int) int) (lambda (x) (if (= x 0) 0 (+ 100 (rd-f (- x 1))))))
(rd-old 3)
(define-effect rd-reads (maxeff spin (read (globals rd-app rd-g))))
(define rd-app (subr rd-reads ((subr rd-reads (int) int) int) int) (lambda (k x) (k x)))
(define* rd-g (subr spin (int) int) (lambda (x) (if (= x 0) 0 (+ 1 (rd-app rd-g (- x 1))))))
(define rd-old-g (subr rd-reads (int) int) rd-g)
(rd-old-g 3)
(define* rd-g (subr spin (int) int) (lambda (x) (if (= x 0) 0 (+ 100 (rd-app rd-g (- x 1))))))
(rd-old-g 3)
