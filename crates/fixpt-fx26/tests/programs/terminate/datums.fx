;;; Datums are made from what exists and never change: their parts are
;;; smaller.
(define size (subr pure (datum) int)
  (letrec ((size (subr pure (datum) int)
             (lambda (d) (if (datum-pair? d) (+ (size (datum-car d)) (size (datum-cdr d))) 1))))
    size))
(size (datum-cons (datum-int 1) (datum-cons (datum-int 2) (datum-int 3))))
