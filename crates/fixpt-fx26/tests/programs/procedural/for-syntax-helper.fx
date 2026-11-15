;; => 7
;; A transformer calls a helper of phase 1's (`begin-for-syntax`), which
;; the namespace it runs in has: defined before it, there alone.
(begin-for-syntax
  (define double (subr pure (datum) datum) (lambda (d) (if (int? d) (* 2 d) d))))
(define-syntax dbl (er-macro-transformer (lambda (form rename compare) (double (car (cdr form))))))
(+ (dbl 3) 1)
