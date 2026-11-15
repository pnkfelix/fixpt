;; A file of macros with phase-1 forms of its own (`begin-for-syntax`),
;; which its macros' transformers call.
(begin-for-syntax
  (define scale (subr pure (datum) datum) (lambda (d) (if (int? d) (* 10 d) d))))
(define-syntax tenfold
  (er-macro-transformer (lambda (form rename compare) (scale (car (cdr form))))))
(define one int 1)
