;;; `letregion`: a region for analysis only, with no place of its own. Its
;;; data is the heap's; what the body does to it is masked, as a `letrena`'s
;;; is, so a procedure that builds and sums a list of its own is pure.
(define total (subr pure (int) int)
  (lambda (n)
    (letregion r
      (letrec ((build (subr (alloc r) (int (listof int r)) (listof int r))
                 (lambda (i acc) (if (= i 0) acc (build (- i 1) (cons i acc)))))
               (sum (subr (read r) ((listof int r) int) int)
                 (lambda (xs acc) (if (null? xs) acc (sum (cdr xs) (+ acc (car xs)))))))
        (sum (build n nil) 0)))))
(total 10)
