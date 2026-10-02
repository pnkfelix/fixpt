;; => #t
;; Procedures of a module that call each other.
(define parity
  (module
    (define-rec
      (even (subr spin (int) bool) (lambda (k) (if (= k 0) #t (odd (- k 1)))))
      (odd (subr spin (int) bool) (lambda (k) (if (= k 0) #f (even (- k 1))))))))
(with parity (even 10))
