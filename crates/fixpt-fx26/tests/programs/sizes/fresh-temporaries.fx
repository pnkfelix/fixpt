;;; Each expansion's own variable is named for what its form does not
;;; mention (`TODO.md` §46): a program that binds the first choice, and the
;;; second, outside the form and uses them inside sees its own bindings.
(define* probe (subr pure ((listof int acyclic) int) int)
  (lambda (xs n)
    (let ((%case-key 1) (%case-key1 2) (%confirm-value 3) (%acyclic-value 4) (%nat-value 5))
      (+ (case n ((7) (+ %case-key %case-key1)) (else 0))
         (+ (confirm-length xs 2 (v %confirm-value) 0)
            (+ (acyclic xs (v %acyclic-value) 0)
               (confirm-nat n (k %nat-value) 0)))))))
(probe (list 1 2) 7)
