;; The file's `scale`, its phase 1's, for its macro; this program's own,
;; of the same name, for this program's: 10 times 4, and 1000 and 4: 1044.
(begin-for-syntax
  (define scale (subr pure (datum) datum) (lambda (d) (if (int? d) (+ 1000 d) d))))
(define lib (load-module "for-syntax.fx"))
(import-with-syntax lib)
(define-syntax thousand-and
  (er-macro-transformer (lambda (form rename compare) (scale (car (cdr form))))))
(+ (tenfold 4) (thousand-and 4))
