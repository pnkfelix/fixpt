; Verified
;;; The shorthand and an `ensures` of its own, both said: the shorthand's
;;; first, and each printed as written. `<` proves both: where `i < n`, `i
;;; ≤ n`.
(define less (subr pure ((i int) (n int)) (bool (then (< 0 1)) (else (<= 1 0)))
               (ensures r (implies r (<= i n))))
  <)
(define* below (subr (read (globals less)) (nat nat) nat)
  (lambda (i n) (if (less i n) (- n i) 0)))
(below 3 10)
