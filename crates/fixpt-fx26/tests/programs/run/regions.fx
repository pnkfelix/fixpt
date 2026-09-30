;;; `letrena` and `letreap`: data made in a region that lives while the
;;; body runs, and only what does not mention the region given back. The
;;; two differ only in how the region's memory is managed (for now only
;;; register code gives a `letrena` a region of its own, and a `letreap`
;;; allocates in the heap); the checker's rule is what is tested.
(define add-to (subr pure (int) int)
  (lambda (n)
    (letrena r
      (let ((b (the (ref int r) (new 0))))
        (begin (set b (+ (get b) n)) (get b))))))

(define total (subr spin (int) int)
  (lambda (n)
    (letreap r
      (letrec ((build (subr (maxeff (alloc r) spin) (int (listof int r)) (listof int r))
                 (lambda (i acc) (if (= i 0) acc (build (- i 1) (cons i acc)))))
               (add-up (subr (maxeff (read r) spin) ((listof int r) int) int)
                 (lambda (xs acc) (if (null? xs) acc (add-up (cdr xs) (+ acc (car xs)))))))
        (add-up (build n nil) 0)))))

(the (listof int @l) (list (add-to 41) (total 100)))
