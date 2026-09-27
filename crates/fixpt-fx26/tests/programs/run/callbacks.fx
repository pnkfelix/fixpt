;;; Procedures written into storage need not say `spin` when they do not read
;;; the region they are kept in: a table of callbacks, each finite, called
;;; through the table, and the whole pure.
(define run-callbacks (subr pure (int) int)
  (lambda (n)
    (letrena t
      (let ((cbs (the (ref (listof (subr pure (int) int) t) t) (rnew t nil))))
        (begin
          (set cbs (rcons t (lambda ((x int)) (+ x 1)) (get cbs)))
          (set cbs (rcons t (lambda ((x int)) (* x 2)) (get cbs)))
          ((car (cdr (get cbs))) ((car (get cbs)) n)))))))
(run-callbacks 20)
