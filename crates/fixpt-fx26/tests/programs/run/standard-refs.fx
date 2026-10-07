;;; `(with #%fx n)` is the standard `n` wherever it is (`TODO.md` §46): a
;;; `case` whose comparisons are shadowed still compares as standard, and
;;; so do the operations a program names through `#%fx` itself, called or
;;; as values, and a `case` in a module's item; each answer a digit of the
;;; score.
(define sm (module (define six (subr pure (int) int) (lambda (n) (case n ((1) 6) (else 0))))))
(define* score (subr (read (globals sm)) () int)
  (lambda ()
    (let ((= (lambda ((a int) (b int)) #t))
          (symbol=? (lambda ((a symbol) (b symbol)) #t))
          (+ (lambda ((a int) (b int)) 0)))
      (let ((d (lambda ((acc int) (k int)) ((with #%fx +) ((with #%fx *) acc 10) k)))
            (add (with #%fx +)))
        (d (d (d (d (d (case 2 ((1) 7) (else 1))
                       (case 'b ((a) 7) ((b) 2) (else 7)))
                    ((with #%fx +) 1 2))
                 (add 2 2))
              (if (= 1 2) 5 6))
           (with sm (six 1)))))))
(score)
