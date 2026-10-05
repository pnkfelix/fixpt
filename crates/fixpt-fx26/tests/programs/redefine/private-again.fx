;;; A program's private regions declared again, as a file loaded again
;;; declares them: the same regions, so a value made before is still one
;;; the procedures defined after take (TODO §30).
(private-regions @q)
(define xs (listof int @q) (cons 1 (cons 2 nil)))
(define* total (subr (maxeff (read @q) spin) ((listof int @q)) int)
  (lambda (l) (if (null? l) 0 (+ (car l) (total (cdr l))))))
(private-regions @q)
(define* total (subr (maxeff (read @q) spin) ((listof int @q)) int)
  (lambda (l) (if (null? l) 0 (+ (* 10 (car l)) (total (cdr l))))))
(total xs)
