; Refused
;;; A test that proves less does not fit where one that proves more is
;;; expected: `<=` where true is not `<`.
(define weaker (subr pure ((i : int) (n : int)) bool (ensures r (implies r (<= i n)))) <)
(define less (subr pure (int int) (bool (then (< 0 1)) (else))) weaker)
(less 1 2)
