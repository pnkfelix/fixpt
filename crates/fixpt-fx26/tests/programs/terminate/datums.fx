;;; Datums are made from what exists and never change: their parts are
;;; smaller.
(define size (subr pure (datum) int)
  (letrec ((size (subr pure (datum) int)
             (lambda (d) (if (pair? d) (+ (size (car d)) (size (cdr d))) 1))))
    size))
(size (cons 1 (cons 2 3)))
