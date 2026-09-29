;;; No function colour: one `for-each`, polymorphic in its argument's effect,
;;; is used with a procedure that suspends (`yield-int`, from
;;; `generator.fx`) and with one that writes a ref. Python needs `for` and
;;; `async for`, and a second copy of any higher-order helper.
(define-effect D (maxeff spin (read @l) (read (globals g yield-int for-each xs))))
(define-type step (productof (v int) (k (composable unit int D @p))))
(define g (prompt-tag int step D @p) (make-continuation-prompt-tag))

(define* yield-int (subr (maxeff (goto @p) (comefrom @p)) (int) unit)
  (lambda (x)
    (call-with-composable-continuation
      (lambda (k) (abort-current-continuation g (product (v x) (k k))))
      g)))

(define for-each
  (poly ((e effect)) (subr (maxeff e spin (read @l)) ((subr e (int) unit) (listof int @l)) unit))
  (plambda ((e effect))
    (lambda (f xs)
      (letrec ((go (subr (maxeff e spin (read @l)) ((listof int @l)) unit)
                 (lambda (ys) (if (null? ys) #u (begin (f (car ys)) (go (cdr ys)))))))
        (go xs)))))

(define* sum-all (subr (maxeff (goto @p) (comefrom @p) (read @l) spin) (step) int)
  (lambda (s)
    (+ (extract s v) (prompt g ((extract s k) #u) (lambda (s2) (sum-all s2))))))

(define xs (listof int @l) (cons 1 (cons 2 (cons 3 nil))))

;; Suspending: each element goes to the consumer, which sums them.
(prompt g (begin (for-each yield-int xs) 0) sum-all)          ; 6

;; Not suspending: the same `for-each`, at the effect (write @r).
(define total (ref int @r) (new 0))
(for-each (lambda (x) (set total (+ x (get total)))) xs)
(get total)                                                   ; 6
