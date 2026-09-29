;;; A generator, and a consumer that sums what it yields.
;;; `yield-int` captures the rest of the producer up to `g`'s prompt and
;;; aborts to the handler with the value and that continuation; the handler
;;; (`sum-all`) adds the value and resumes the producer under a new prompt.
(define-effect D (maxeff spin (read (globals g yield-int count-up))))
(define-type step (productof (v int) (k (composable unit int D @p))))
(define g (prompt-tag int step D @p) (make-continuation-prompt-tag))

(define* yield-int (subr (maxeff (goto @p) (comefrom @p)) (int) unit)
  (lambda (x)
    (call-with-composable-continuation
      (lambda (k) (abort-current-continuation g (product (v x) (k k))))
      g)))

(define* count-up (subr (maxeff (goto @p) (comefrom @p) spin) (int int) unit)
  (lambda (i n)
    (if (> i n) #u (begin (yield-int i) (count-up (+ i 1) n)))))

(define* sum-all (subr (maxeff (goto @p) (comefrom @p) spin) (step) int)
  (lambda (s)
    (+ (extract s v) (prompt g ((extract s k) #u) (lambda (s2) (sum-all s2))))))

(prompt g (begin (count-up 1 4) 0) sum-all)   ; 1+2+3+4 = 10
