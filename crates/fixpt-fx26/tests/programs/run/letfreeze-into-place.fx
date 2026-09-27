;;; `(letfreeze (r a) body …)`: a list built, and changed, at region `r` in
;;; arena `a`, frozen into `a` as the `letfreeze` ends: `(listof int (const
;;; a))`, which nothing may write, and which won't outlive `a`.
(define total (subr pure (int) int)
  (lambda (n)
    (letrena a
      (let ((xs (letfreeze (r a)
                  (let ((ys (the (listof int r) (rcons a n (rcons a 2 nil)))))
                    (begin (set-car! ys (+ n 1)) ys)))))
        (+ (car xs) (car (cdr xs)))))))
(total 5)
