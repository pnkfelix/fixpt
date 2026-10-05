;; => #t
;; Procedures calling each other, in order, with no `define-rec`; a value
;; made from them after both (`DONE.md` §37).
(define parity (module
  (define even? (subr spin (int) bool) (lambda (n) (if (= n 0) #t (odd? (- n 1)))))
  (define odd? (subr spin (int) bool) (lambda (n) (if (= n 0) #f (even? (- n 1)))))
  (define ten-even bool (even? 10))))
(with parity ten-even)
