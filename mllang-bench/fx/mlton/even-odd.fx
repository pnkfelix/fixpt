;;; EVEN-ODD -- parity by mutual recursion, counting down one at a time.
;;;
;;; From MLton's benchmark suite (benchmark/tests/even-odd.sml, commit
;;; aa2fd1ad9b91), ported to FX-26. Iteration count (ours; MLton's driver
;;; was not fetched): 1 iterations of (even 500000000) and
;;; (odd 500000000).
;;; Answer: #t. The original checks that (even n) is (not (odd n)); here
;;; each iteration's value is (and (even n) (not (odd n))), both computed,
;;; which for n = 500000000 is #t.
;;; SML's `local` helpers even' and odd' are a define-rec.

(define-rec
  (even* (subr (maxeff spin (read (globals even* odd*))) (int) bool) (lambda (i) (if (= i 0) #t (odd* (- i 1)))))
  (odd* (subr (maxeff spin (read (globals even* odd*))) (int) bool) (lambda (i) (if (= i 0) #f (even* (- i 1))))))

(define abs (subr pure (int) int) (lambda (i) (if (< i 0) (- 0 i) i)))
(define* even (subr spin (int) bool) (lambda (i) (even* (abs i))))
(define* odd (subr spin (int) bool) (lambda (i) (odd* (abs i))))

;; The inputs, where no compiler can fold them: globals, which a later
;; definition may replace.
(define input int 500000000)
(define iterations int 1)

(define* run (subr spin (int bool) bool)
  (lambda (i result)
    (if (= i 0)
        result
        (run (- i 1)
             (let ((e (even input)) (o (odd input)))
               (and e (not o)))))))
(run iterations #f)
