;;; A group of procedures that call each other: each reads the other's
;;; global, and so, calling it, its own too: both say so.
(define-rec
  (ev (subr (maxeff spin (read (globals ev od))) (int) bool)
    (lambda (n) (if (= n 0) #t (od (- n 1)))))
  (od (subr (maxeff spin (read (globals ev od))) (int) bool)
    (lambda (n) (if (= n 0) #f (ev (- n 1))))))
(ev 10)
