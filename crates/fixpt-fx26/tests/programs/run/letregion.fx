;;; `letregion`: data made in a region that lives while the body runs, and
;;; only what does not mention the region given back. Its allocation is the
;;; heap's for now; the checker's rule is what is tested.
(define add-to (subr pure (int) int)
  (lambda (n)
    (letregion r
      (let ((b (the (ref int r) (new 0))))
        (begin (set b (+ (get b) n)) (get b))))))

(define total (subr pure (int) int)
  (lambda (n)
    (letregion r
      (letrec ((build (subr (alloc r) (int (listof int r)) (listof int r))
                 (lambda (i acc) (if (= i 0) acc (build (- i 1) (cons i acc)))))
               (sum (subr (read r) ((listof int r) int) int)
                 (lambda (xs acc) (if (null? xs) acc (sum (cdr xs) (+ acc (car xs)))))))
        (sum (build n nil) 0)))))

(the (listof int @l) (cons (add-to 41) (cons (total 100) nil)))
