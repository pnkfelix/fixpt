;; => -1
;; `pselect` waits for a key (`TODO.md` §95) or a message, or no longer than
;; a deadline already passed. A test's standard input is empty, at its end,
;; which a read does not wait for, so the key's arm, the first ready, is
;; chosen and gets `eof`; a terminal's, with no key yet, the deadline's: -1
;; either way.
(define-type byte-result (sumof (byte u8) (eof unit) (failed io-error)))
(define* code (subr pure (byte-result) int)
  (lambda (b) (tagcase b (byte k (u8->int k)) (eof u -1) (failed e -2))))
(define never (icell int @c) (make-icell))
(pselect ((icell-get never) x x) ((read-byte) b (code b)) ((sleep-until (clock)) u -1))
