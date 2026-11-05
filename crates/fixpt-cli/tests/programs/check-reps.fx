;;; `fixpt check --reps` (`dialects.rs`): a definition, a `define-rec`'s
;;; two, an expression (no line), then a form refused, which ends the lines.
(define n 3)
(define-rec
  (even? (subr (maxeff (read @globals) spin) (int) bool)
         (lambda (k) (if (= k 0) #t (odd? (- k 1)))))
  (odd? (subr (maxeff (read @globals) spin) (int) bool)
        (lambda (k) (if (= k 0) #f (even? (- k 1))))))
(even? n)
(define bad (+ 1 #t))
(define after 4)
