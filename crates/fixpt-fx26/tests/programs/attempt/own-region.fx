;; => 3
;; A body may write what it allocates in a region of its own: masked,
;; that is nothing another could see.
(define* count (subr (maxeff (read @h) spin) ((listof int @h)) int)
  (lambda (l)
    (letregion r
      (let ((n (the (ref int r) (new 0))))
        (letrec ((go (subr (maxeff (read @h) (read r) (write r) spin) ((listof int @h)) int)
                   (lambda (l) (if (null? l) (get n) (begin (set n (+ (get n) 1)) (go (cdr l)))))))
          (go l))))))
(attempt (count (list 1 2 3)) (lambda ((m string)) -1))
