; Verified
;;; A loop: the self tail call is a jump back to the word's start, and the
;;; `requires` is its invariant. The tail call's `ensures` entails the
;;; caller's: `r = (acc + 1) + (n - 1)` is `r = acc + n`.
(define count (subr (maxeff (read (globals count)) spin) ((n int) (acc int)) int
                (requires (<= 0 n))
                (ensures r (= r (+ acc n))))
  (lambda (n acc) (if (= n 0) acc (count (- n 1) (+ acc 1)))))
(count 10 5)
