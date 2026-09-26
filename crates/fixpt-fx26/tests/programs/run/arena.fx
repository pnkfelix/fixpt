;;; A `letrena` whose list is made in its region, in the procedure that
;;; enters it: as register code, in the heap's regions; its sum given back.
;;; Called many times, so that regions are entered, filled and ended again.
(define sum3 (subr pure (int) int)
  (lambda (n)
    (letrena r
      (let ((xs (the (listof int r) (cons n (cons (+ n 1) (cons (+ n 2) nil))))))
        (+ (car xs) (+ (car (cdr xs)) (car (cdr (cdr xs)))))))))

(define total (subr pure (int int) int)
  (lambda (i acc) (if (= i 0) acc (total (- i 1) (+ acc (sum3 i))))))

(total 1000 0)
