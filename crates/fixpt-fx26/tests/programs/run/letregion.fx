;;; `letregion`: a region for analysis only, with no place of its own. Its
;;; data is the heap's; what the body does to it is masked, as a `letrena`'s
;;; is, so a procedure that builds and sums a list of its own says only
;;; that it may not end (a count down, a list walked).
(define total (subr spin (int) int)
  (lambda (n)
    (letregion r
      (letrec ((build (subr (maxeff (alloc r) spin) (int (listof int r)) (listof int r))
                 (lambda (i acc) (if (= i 0) acc (build (- i 1) (cons i acc)))))
               (add-up (subr (maxeff (read r) spin) ((listof int r) int) int)
                 (lambda (xs acc) (if (null? xs) acc (add-up (cdr xs) (+ acc (car xs)))))))
        (add-up (build n nil) 0)))))
(total 10)
