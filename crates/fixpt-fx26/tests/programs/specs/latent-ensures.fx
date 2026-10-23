; Verified
;;; What a test proves is an `ensures` of its result: `(bool (then P …)
;;; (else Q …))` is `(ensures r (and (implies r (and P …)) (implies (not r)
;;; (and Q …))))`. An alias of `<` at the `ensures` written out narrows as
;;; one at the shorthand does (`sizes/latent-alias.fx`): `(- n i)` a `nat`.
(define less (subr pure ((i int) (n int)) bool
               (ensures r (and (implies r (< i n)) (implies (not r) (<= n i)))))
  <)
(define* below (subr (read (globals less)) (nat nat) nat)
  (lambda (i n) (if (less i n) (- n i) 0)))
(below 3 10)
