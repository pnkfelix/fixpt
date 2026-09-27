;;; A group of top-level procedures that call each other (`define-rec`): a
;;; top-level `letrec`, whose names are in scope in all its lambdas and in
;;; what follows.
(define-rec
  (ev (subr spin (int) bool) (lambda (n) (if (= n 0) #t (od (- n 1)))))
  (od (subr spin (int) bool) (lambda (n) (if (= n 0) #f (ev (- n 1)))))
  ;; A loop, in the group: its tail call of itself jumps.
  (count (subr spin (int int) int) (lambda (i acc) (if (= i 0) acc (count (- i 1) (+ acc (if (ev i) 1 0)))))))

(define evens (subr spin (int) int) (lambda (n) (count n 0)))

(the (listof int @l) (cons (evens 1000) (cons (if (od 7) 1 0) nil)))
