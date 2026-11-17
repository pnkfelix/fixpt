;; => (2 1)
;; A path of paths, `(with (with outer mid) a)`; and a path from a
;; parameter, whose module the call names.
(define make
  (lambda ()
    (module
      (define-generative t int #:seal up #:unseal down)
      (define zero t (up 0))
      (define inc (subr pure (t) t) (lambda (c) (up (+ (down c) 1))))
      (define value (subr pure (t) int) (lambda (c) (down c))))))
(define outer (module (define mid (module (define a (make))))))
(define start (with (with (with outer mid) a) zero))
(define q (with outer mid))
(define bump (lambda ((x (select (with (with outer mid) a) t))) ((with (with q a) inc) x)))
(define once
  (lambda ((o (moduleof (val a (moduleof (abs t type) (val zero t) (val inc (subr pure (t) t))
                                         (val value (subr pure (t) int)))))))
    (let ((p (with o a))) ((with p value) ((with (with o a) inc) (with p zero))))))
(list ((with (with (with outer mid) a) value) (bump (bump start))) (once q))
